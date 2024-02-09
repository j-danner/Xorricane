#include <iostream>
#include <stack>
#include <deque>
#include <set>
#include <queue>
#include <omp.h>

#include "solver.hpp"

solver::solver(const vec< vec<xlit> >& clss, const var_t num_vars, const options& opt_) noexcept : opt(opt_) {
    #ifndef NDEBUG
        if(opt.verb==0) opt.verb = 100;
    #endif

    //init watch_list
    watch_list.resize(num_vars+1);
    L_watch_list.resize(num_vars+1);
    //assignments_list.resize(opt_.num_vars+1);
    
    lineral_watches = vec<std::list<xlit_watch>>(num_vars+1, std::list<xlit_watch>() );
    
    // init assignments
    alpha = vec<bool3>(num_vars + 1, bool3::None);
    alpha_dl = vec<var_t>(num_vars + 1, (var_t) -1);
    alpha_trail_pos = vec<var_t>(num_vars + 1, (var_t) -1);
    equiv_lits = vec<equivalence>(num_vars+1);
    equiv_lits_dl = vec<var_t>(num_vars+1, (var_t) -1);
    dl_count = vec<dl_c_t>(num_vars+1, 1); 
    trails = vec< std::list<trail_elem> >();
    trails.reserve(num_vars+1);
    trails.emplace_back( std::list<trail_elem>() );
    total_trail_length = 1;
    last_phase = vec<bool3>(num_vars + 1, bool3::None);
    //init last_phase according to init_phase of guessing_path:
    for(var_t idx=0; idx<opt_.P.size(); ++idx) {
        last_phase[opt_.P[idx]] = to_bool3( opt_.P.get_phase(idx) );
    }

    // vec of pure literals
    vec<xlit> _L = vec<xlit>();

    xclss = vec<xcls_watch>(0);
    xclss.reserve(clss.size());
    
    utility = vec<double>(0);
    utility.reserve(clss.size());

    // temporarily store clss in _xclss - before init of xclss we might want to reduce with pure literals in _L (!)
    vec<xcls> _xclss;
    _xclss.reserve(clss.size());
    active_cls = 0; //value is managed by 'init_and_add_xcls_watch'

    // run through xor-clauses to find lineq and construct watch-literals
    for (var_t i = 0; i < clss.size(); i++) {
        xcls cls = xcls(clss[i]); 
        //check if clause reduces to unit
        if (cls.deg() == 1) { // lin-eq!
            _L.emplace_back( cls.get_ass_VS().get_non_zero_el().add_one() );
        }
        if (!cls.is_zero()) _xclss.emplace_back( std::move(cls) );
    }
    //reduce xclss with _L
    xsys _Lsys(_L);
    for(auto& cls : _xclss) {
        switch(opt.ip) {
            case initial_prop_opt::no:
                break;
            case initial_prop_opt::nbu:
                cls.update_short(_Lsys);
                break;
            case initial_prop_opt::full:
                cls.update(_Lsys);
                break;
        }
        init_and_add_xcls_watch( std::move(cls), false );
    }

    assert(active_cls == xclss.size() - lineral_queue.size());

    //init order_heap and activity_score
    activity_score = vec<double>(num_vars + 1, 1);
    for (var_t i = 0; i < num_vars+1; i++) {
        activity_score[i] += watch_list[i].size();
    }
    for(var_t i = 1; i<=num_vars; ++i) {
        order_heap_vsids.insert( i );
    }
    

    // init active_cls_stack
    active_cls_stack = vec<var_t>();
    active_cls_stack.emplace_back(active_cls);

    //init restart params
    update_restart_schedule(0);

    assert(assert_data_structs());
};

void solver::backtrack(const var_t& lvl) {
    VERB(90, "BACKTRACK start");
    if(lvl == dl) return;
    assert(lvl < dl);
    VERB(80, "c backtracking to dl " << lvl);
    if (dl - lvl > 1) {
        VERB(80, "c " << std::to_string(dl) << " : BACKJUMPING BY MORE THAN ON LEVEL!");
    }
    
    // trail and assignments!
  #ifndef NDEBUG
    print_trail();
    print_assignments();
  #endif

    // update dl_count
    for(var_t dl_ = dl; dl_>lvl; dl_--) dl_count[dl_]++;
    //undo unit linerals, revert assignments and alpha, and reset trail, reasons, queue
    while(dl>lvl) {
        while(!TRAIL.empty()) { pop_trail(); };
        trails.pop_back();
        lineral_watches[dl].clear();
        assert(lineral_watches[dl].empty());
        //adapt dl
        --dl;
        //restore active_cls count
        active_cls = active_cls_stack.back();
        active_cls_stack.pop_back();
    }
    assert(dl==lvl);

    //cleanup lineral_queue
    lineral_queue.clear();

    // check active_cls count
    //VERB(90, "active_cls restored:   " + std::to_string(active_cls))
    //VERB(90, "active_cls recomputed: " + std::to_string(std::count_if(xclss.begin(), xclss.end(), [&](const xcls_watch &xcls_w) { return xcls_w.is_active(dl_count) && xcls_w.is_irredundant(); })))
    assert(active_cls == (var_t) std::count_if(xclss.begin(), xclss.end(), [&](const xcls_watch &xcls_w) { return xcls_w.is_active(dl_count) && xcls_w.is_irredundant(); }));

  #ifndef NDEBUG
    print_trail();
    print_assignments();
  #endif

    VERB(201, to_str());
    VERB(90, "BACKTRACK end");
    assert(assert_data_structs());
};

// decision heuristics
xlit solver::dh_vsids() {
    assert(!order_heap_vsids.empty());
    var_t ind = 0;
    while (ind==0 || (alpha[ind] != bool3::None && !order_heap_vsids.empty() )) {
        ind = order_heap_vsids.removeMin();
    }
    return xlit( ind, last_phase[ind]==bool3::True);
};

xlit solver::dh_shortest_wl() {
    //find unassigned variable that has the longest watch_list
    var_t lt_min = 0;
    size_t size_min = xclss.size() + 1;
    for(size_t idx=1; idx<watch_list.size(); ++idx) {
        if(alpha[idx]==bool3::None && (watch_list[idx].size() < size_min)) {
            lt_min = idx; size_min = watch_list[idx].size();
        }
    }
    assert(lt_min!=0 && lt_min < (var_t)alpha.size());
    return xlit( lt_min, last_phase[lt_min]==bool3::True);
}

xlit solver::dh_longest_wl() {
    //find unassigned variable that has the longest watch_list
    var_t lt_max = 0;
    size_t size_max = 0;
    for(size_t idx=1; idx<watch_list.size(); ++idx) {
        if(alpha[idx]==bool3::None && (watch_list[idx].size() > size_max)) {
            lt_max = idx; size_max = watch_list[idx].size();
        }
    }
    assert(lt_max!=0 && lt_max < (var_t)alpha.size());

    return xlit( lt_max, last_phase[lt_max]==bool3::True);
}

xlit solver::dh_lex_LT() {
    var_t i = 1;
    while(alpha[i] != bool3::None) ++i;
    assert(i<alpha.size());
    return xlit( i, last_phase[i]==bool3::True);
};

template<const solver::dec_heu_t dh>
xlit solver::dh_gp() {
    var_t idx = 0;
    while (idx < opt.P.size() && alpha[opt.P[idx]] != bool3::None) ++idx;
    if(idx == opt.P.size()) return (this->*dh)();
    const var_t i = opt.P[idx];
    assert(i>0 && alpha[i]==bool3::None);
    return xlit(i, last_phase[i] == bool3::True);
}


void solver::bump_score(const var_t &ind) {
    assert(ind < activity_score.size());
    activity_score[ind] += bump;
    max_act_sc = std::max(max_act_sc,  activity_score[ind]);

    if(activity_score[ind] > 1e100) {
        for (auto& v: activity_score) v *= 1e-100;
        max_act_sc *= 1e-100;
        bump *= 1e-100;
    }

    // Update order_heap with respect to new activity
    if (order_heap_vsids.inHeap(ind)) {
        order_heap_vsids.decrease(ind);
    }
};

void solver::bump_score(const xlit &lit) {
    assert(lit.LT() < activity_score.size());
    bump_score(lit.LT());
};

void solver::bump_score(const xsys &new_xsys) {
    for (const auto &[lt, _] : new_xsys.get_pivot_poly_idx()) {
        assert(lt < activity_score.size());
        bump_score(lt);
    }
};

void solver::decay_score() {
    //instead of actually decaying all scores; we increase the bump
    bump *= (1.0 / decay);
};

xlit unit;
std::pair<var_t, xcls_watch> solver::analyze_exp() {
    VERB(70, "**** analyzing conflict");
#ifndef NDEBUG
    print_assignments("    *");
    print_trail("    *");
#endif
    assert( trails.back().back().ind == 0 ); //ensure last trail entry is a conflict & it comes from an actual clause

    //go through trail of current dl -- skip over irrelevant parts
    xcls_watch_resolver learnt_cls = get_reason(TRAIL.back());
    assert(learnt_cls.is_unit(dl_count));
    VERB(70, "   * reason clause " + learnt_cls.to_str() + " for UNIT " + learnt_cls.get_unit().to_str() );
    bump_score( TRAIL.back().ind );
    pop_trail(); //remove conflict from trail, i.e., now we should have alpha[0]==bool3:None
    
    //as long as assigning_lvl is dl OR -1 (i.e. equiv-lits are used!), resolve with reason clauses
    while( learnt_cls.get_assigning_lvl(alpha_dl) == dl || learnt_cls.get_assigning_lvl(alpha_dl) == (var_t) -1 ) {
        assert(!TRAIL.empty());
        VERB(70, "   * conflict clause is " + learnt_cls.to_str());
        VERB(70, "   '----> gives with current assignments: " + learnt_cls.to_xcls().reduced(alpha).to_str());

        unit = std::move(learnt_cls.get_unit());
        unit.reduce(alpha);
        assert( unit.is_one() );
        assert(!learnt_cls.to_xcls().is_zero());

        //pop trail until we are at the implied alpha that is watched by learnt_cls (by wl1)
        while( (TRAIL.back().type != trail_t::IMPLIED_ALPHA) || !learnt_cls.unit_contains(TRAIL.back().ind) ) {
            pop_trail();
        }
        assert(TRAIL.back().type == trail_t::IMPLIED_ALPHA);
        
        //get reason_cls
        const auto& reason_cls = get_reason(TRAIL.back());
        VERB(70, "   * reason clause " + reason_cls.to_str() + " for UNIT " + reason_cls.get_unit().to_str() );
    #ifndef NDEBUG
        //ensure that reason cls is reason for provided alpha
        xlit unit = reason_cls.get_unit();
        unit.reduce(alpha);
        unit.reduce(equiv_lits, equiv_lits_dl, 0);
        assert(unit.is_zero()); //unit MUST reduce to zero, as TRAIL is not yet popped
    #endif
        bump_score( TRAIL.back().ind );
        pop_trail(); //remove from trail!

        learnt_cls.resolve( reason_cls, alpha, alpha_dl, alpha_trail_pos, dl_count);
    }
    
    VERB(70, "   * ");
    VERB(70, "   * learnt clause is " + BOLD( learnt_cls.to_str() ) );
    VERB(70, "   '----> gives with current assignments: " + learnt_cls.to_xcls().reduced(alpha).to_str());

#ifndef NDEBUG
    //print_assignments("    *");
    //print_trail("    *");
#endif

    //TODO
    //CLAUSE MINIMIZATION!

    //find correct backtrack-lvl
    const var_t b_lvl = learnt_cls.get_assigning_lvl(alpha_dl);
    if( dl < learnt_cls.size() && b_lvl == dl-1 ) {
        VERB(50, "   * negated decisions lead to smaller learnt_cls and the same backtrack-level!");
        //assert(false);
        
    }
    
    VERB(70, "****");
    return std::pair<var_t, xcls_watch>(b_lvl, learnt_cls);
};

std::pair<var_t, xcls_watch> solver::analyze() {
    VERB(70, "**** analyzing conflict");
#ifndef NDEBUG
    print_assignments("    *");
    print_trail("    *");
#endif
    assert( trails.back().back().ind == 0 ); //ensure last trail entry is a conflict & it comes from an actual clause

    //go through trail of current dl -- skip over irrelevant parts
    xcls_watch_resolver learnt_cls = get_reason(TRAIL.back());
    //xcls_watch learnt_cls = get_reason(TRAIL.back());

    assert(learnt_cls.is_unit(dl_count));
    VERB(70, "   * reason clause is   " + BOLD( learnt_cls.to_str() ) + " for UNIT " + learnt_cls.get_unit().to_str() );
    bump_score( TRAIL.back().ind );
    pop_trail(); //remove conflict from trail, i.e., now we should have alpha[0]==bool3:None

    //as long as assigning_lvl is dl OR -1 (i.e. equiv-lits are used!), resolve with reason clauses
    while( learnt_cls.get_assigning_lvl(alpha_dl) == dl || learnt_cls.get_assigning_lvl(alpha_dl) == (var_t) -1 ) {
        assert(!TRAIL.empty());
        VERB(70, "   * conflict clause is " + BOLD( learnt_cls.to_str() ) + "   --> gives with current assignments: " + learnt_cls.to_xcls().reduced(alpha).to_str());
        
        unit = std::move(learnt_cls.get_unit());
        unit.reduce(alpha);
        assert( unit.is_one() );
        assert(!learnt_cls.to_xcls().is_zero());

        //pop trail until we are at the implied alpha that is watched by learnt_cls (by wl1)
        while( (TRAIL.back().type != trail_t::IMPLIED_ALPHA) || !learnt_cls.unit_contains(TRAIL.back().ind) ) {
            assert(!TRAIL.empty());
            pop_trail();
        }
        assert(TRAIL.back().type == trail_t::IMPLIED_ALPHA);
        
        //get reason_cls
        const auto reason_cls = get_reason(TRAIL.back());
        VERB(70, "   * reason clause is   " + BOLD( reason_cls.to_str() ) + " for UNIT " + reason_cls.get_unit().to_str() );
    #ifndef NDEBUG
        //ensure that reason cls is reason for provided alpha
        unit = reason_cls.get_unit();
        unit.reduce(alpha);
        unit.reduce(equiv_lits, equiv_lits_dl, dl);
        unit.reduce(alpha);
        if(!unit.is_zero()) {
            unit = reason_cls.get_unit();
            unit.reduce(equiv_lits, equiv_lits_dl, dl);
            unit.reduce(alpha);
        }
        assert(unit.is_zero()); //unit MUST reduce to zero, as TRAIL is not yet popped
    #endif
        learnt_cls.resolve( reason_cls, alpha, alpha_dl, alpha_trail_pos, dl_count);

        bump_score( TRAIL.back().ind );
        pop_trail(); //remove from trail!
    }
    // clean-up trail!
    
    VERB(70, "   * ");
    VERB(70, "   * learnt clause is " + learnt_cls.to_str());
    VERB(90, "   * XNF " + learnt_cls.to_xnf_str() );
    VERB(70, "   '----> gives with current assignments: " + learnt_cls.to_xcls().reduced(alpha).to_str());

#ifndef NDEBUG
    print_assignments("    *");
    print_trail("    *");
#endif

    //TODO
    //CLAUSE MINIMIZATION!

    //find correct backtrack-lvl
    const var_t b_lvl = learnt_cls.get_assigning_lvl(alpha_dl);
    if( dl < learnt_cls.size() && b_lvl == dl-1 ) {
        VERB(50, "   * negated decisions lead to smaller learnt_cls and the same backtrack-level!");
        //assert(false);
    }
    
    VERB(70, "****");
    return std::pair<var_t, xcls_watch>(b_lvl, learnt_cls.finalize());
    //return std::pair<var_t, xcls_watch>(b_lvl, learnt_cls);
};

std::pair<var_t, xcls_watch> solver::analyze_no_sres() { return analyze_dpll(); };

std::pair<var_t, xcls_watch> solver::analyze_dpll() {
    VERB(60, "analyze_dpll called!")
#ifndef NDEBUG
    print_assignments("    *");
    print_trail("    *");
#endif
    //return negation of last decision!
    assert(!TRAIL.empty());
    //if trail is empty, we are at dl 0, i.e., analyze_dpll should not be called!
    std::list<xlit> xlits;
    for(auto tr = trails.begin()+1; tr!=trails.end(); ++tr) {
        if(!tr->empty()) xlits.emplace_back( tr->front().ind, !b3_to_bool(alpha[tr->front().ind]) );
    }
    xcls learnt_cls( std::move(xlits) );
    VERB(70, "   * learnt clause is " + learnt_cls.to_str());

    return {dl>0 ? dl-1 : 0, std::move(learnt_cls) };
};

//code from CMS5!
double luby(double y, int x) {
    int size = 1;
    int seq;
    for(seq = 0 ; size < x + 1 ; seq++) {
        size = 2 * size + 1;
    }

    while (size - 1 != x) {
        size = (size - 1) >> 1;
        seq--;
        x = x % size;
    }

    return std::pow(y, seq);
}

bool solver::need_restart() const {
    return confl_this_restart > confl_until_restart;
};

void solver::update_restart_schedule(const unsigned int &no_restarts) {
    //update confl_until_restart
    switch(get_const_opts()->rst) {
        case restart_opt::no:
            confl_until_restart = (unsigned int) -1;
            break;
        case restart_opt::fixed:
            confl_until_restart = confl_until_restart_default;
            break;
        case restart_opt::luby:
            confl_until_restart = luby(2, no_restarts) * confl_until_restart_default;
            break;
    }
};

void solver::restart(stats& s) {
    VERB(50, "c restart")
    ++s.no_restarts;
    confl_this_restart = 0;

    //go to dl 0
    const unsigned int no_cls = xclss.size();
    backtrack(0);

    //update util_cutoff -- TODO should we use quantiles?
    double avg_util_redundant = 0;
    for(var_t i=0; i<xclss.size(); ++i) {
        if(!xclss[i].is_irredundant()) avg_util_redundant += utility[i];
    }
    avg_util_redundant /= active_cls;
    util_cutoff = decay*avg_util_redundant;
    //rm 'useless' cls:
    VERB(50, "c clean clause database")
    //mark clauses to be deleted
    for(var_t i=0; i<xclss.size(); ++i) {
        if(!xclss[i].is_irredundant() && utility[i] < util_cutoff && xclss[i].is_active(dl_count)) {
            xclss[i].mark_for_removal();
        }
    }
    VERB(50, "c rm clauses")
    assert_slow( assert_data_structs() );
    //remove all clss marked for removal
    vec<xcls_watch> cpy; cpy.reserve(xclss.size());
    vec<double> util_cpy(utility.size(), 0);
    for(var_t i=0; i<xclss.size(); ++i) {
        if(!xclss[i].is_marked_for_removal()) {
            cpy.emplace_back(std::move(xclss[i]));
            util_cpy[i] = utility[i];
        }
    }
    xclss = std::move(cpy);
    utility = std::move(util_cpy);
    VERB(50, "c re-init watch_lists")
    //empty watchlists
    for(auto& wl : watch_list) wl.clear();
    //re-fill watchlists!
    for(var_t i=0; i<xclss.size(); ++i) {
        if(xclss[i].size()>0) watch_list[xclss[i].get_wl0()].emplace_back( i );
        if(xclss[i].size()>1) watch_list[xclss[i].get_wl1()].emplace_back( i );
    }
    assert( assert_data_structs() );
    
    VERB(50, "c removed " + std::to_string( (double) (no_cls / xclss.size()) ) + "\% clauses.")

    update_restart_schedule(s.no_restarts);
    VERB(90, "c restart finished")
};

void solver::remove_fixed_alpha(const var_t upd_lt) {
    VERB(90, "c remove_fixed_alpha start" );
    assert( alpha[upd_lt]!=bool3::None && alpha_dl[upd_lt]==0 );
    assert(dl==0);
    const bool3 val = alpha[upd_lt];
    //rm upd_lt from lineral_watches[0] (all other levels are empty!)
    for(auto& lin_watch : lineral_watches[0]) {
        if(lin_watch.is_active(alpha) && !lin_watch.watches(upd_lt)) {
            lin_watch.rm(upd_lt, val);
        }
    }
    //rm upd_lt from xclss
    for(auto& xcls_w : xclss) {
        if(xcls_w.is_active(dl_count)) {
            assert(!xcls_w.watches(upd_lt));
            if( xcls_w.rm(upd_lt, val) ) decr_active_cls(&xcls_w - &xclss[0]);
        }
    }
    VERB(90, "c remove_fixed_alpha end" );
}

void solver::remove_fixed_equiv([[maybe_unused]] const var_t idx) {
    return;
    //@todo think about best approach to do this!

    VERB(90, "c remove_fixed_equiv start" );
    assert(equiv_lits[idx].is_active());
    assert(dl==0);
    //rm upd_lt from lineral_watches[0] (all other levels are empty!)
    for(xlit_w_it lin = lineral_watches[0].begin(); lin!=lineral_watches[0].end(); ++lin) {
        if(lin->is_active(alpha) && !lin->is_equiv()) {
            if( lin->reduce(alpha, alpha_dl, dl_count, equiv_lits) ) {
                //watch-lists need to be fixed
                if(lin->size()>0) L_watch_list[ lin->get_wl0() ].emplace_back( dl, lin, dl_count[dl] );
                if(lin->size()>1) L_watch_list[ lin->get_wl1() ].emplace_back( dl, lin, dl_count[dl] );
            }
        }
    }
    //rm upd_lt from xclss
    for(auto& xcls_w : xclss) {
        if(xcls_w.is_active(dl_count)) {
            //@todo
            //assert(!xcls_w.watches(upd_lt));
            //if( xcls_w.rm(upd_lt, val) ) decr_active_cls(&xcls_w - &xclss[0]);
        }
    }
    VERB(90, "c remove_fixed_equiv end" );
}

xlit new_unit;
//perform full GCP -- does not stop if conflict is found -- otherwise assert_data_struct will fail!
void solver::GCP(stats &s) {
    s.no_gcp++;
    VERB(90, "GCP start");
    while(!lineral_queue.empty() && no_conflict()) {
        const var_t upd_lt = propagate_implied_lineral();
        if(upd_lt == (var_t) -1) continue; //nothing new to propagate!
        if(upd_lt == 0) { assert(!no_conflict()); continue; } //at conflict!

        {
        //find new implied alphas! -- propagate to watched units
        auto it = L_watch_list[upd_lt].begin();
        while(it != L_watch_list[upd_lt].end()) {
          const auto [lvl, lin, dl_c] = *it;
          auto& lin_w = *lin;
          //if lin_w has been removed and possibly, we have to fix the watching scheme now!
          if(dl_count[lvl] != dl_c) {
              it = L_watch_list[upd_lt].erase( it );
              continue;
          }
          assert(lin_w.watches(upd_lt));
          if(!lin_w.is_active(dl_count)) { ++it; continue; }
          const auto& [new_wl, ret] = lin_w.update(upd_lt, alpha, dl, dl_count);
          //if watched-literal has changed, i.e., new_wl != 0; update watch-list
          if(new_wl != upd_lt) {
              //rm *it from current watch-list:
              it = L_watch_list[upd_lt].erase( it );
              //add i to newly watched literal:
              L_watch_list[new_wl].push_back({lvl, lin, dl_c});
          } else {
              ++it;
          }
          switch (ret) {
          case xlit_upd_ret::ASSIGNING:
            {
              assert( lin_w.is_assigning(alpha) );
              assert( !lin_w.is_active(alpha) );
              // update alpha
              queue_implied_alpha(lin);
            }
            break;
          case xlit_upd_ret::UNIT:
              assert(!lin_w.is_assigning(alpha));
              break;
          }
        }
        }

        {
        auto it = watch_list[upd_lt].begin();
        while(it != watch_list[upd_lt].end()) {
            if (s.cancelled.load()) {
                VERB(10, "c cancelled");
                return;
            }
            //assert(assert_data_structs());
            const var_t i = *it;
            assert(xclss[i].watches(upd_lt));
            if(!xclss[i].is_active(dl_count)) { ++it; continue; }
            const auto& [new_wl, ret] = xclss[i].update(upd_lt, alpha, alpha_dl, alpha_trail_pos, dl_count);
            //if watched-literal has changed, i.e., new_wl != 0; update watch-list
            if(new_wl != upd_lt) {
                //rm *it from current watch-list:
                it = watch_list[upd_lt].erase(it);
                //add i to newly watched literal:
                watch_list[new_wl].push_back(i);
            } else {
                ++it;
            }
            switch (ret) {
            case xcls_upd_ret::SAT:
                assert(xclss[i].is_sat(dl_count));
                assert(xclss[i].is_inactive(dl_count));
                //assert(xclss[i].is_inactive(alpha));
                // IGNORE THIS CLAUSE FROM NOW ON
                decr_active_cls(i);
                break;
            case xcls_upd_ret::UNIT: //includes UNSAT case (i.e. get_unit() reduces with assignments to 1 !)
                assert(xclss[i].is_unit(dl_count));
                assert(xclss[i].is_inactive(dl_count));
                assert(xclss[i].get_unit_at_lvl() == dl);
                //assert(xclss[i].is_inactive(alpha));
                //increase utility
                utility[i]++;
                // IGNORE THIS CLAUSE FROM NOW ON
                decr_active_cls(i);
                // NEW LIN-EQS
                new_unit = std::move(xclss[i].get_unit());
                // add to lineral_watches
                lineral_watches[dl].emplace_back( std::move(new_unit), alpha, alpha_dl, dl_count, i );
                queue_implied_lineral( std::prev(lineral_watches[dl].end()) );
                ++s.new_px_upd;
                break;
            case xcls_upd_ret::NONE:
                //assert(xclss[i].is_none(alpha));
                assert(xclss[i].is_none(dl_count));
                assert(xclss[i].is_active(dl_count));
                break;
            }
        }
        }
        
        //if we propagated on dl 0, remove all upd_lt from lineral_watches AND from xclss, so that they only occur in the watched clauses.
        if(dl == 0) { remove_fixed_alpha(upd_lt); };
        assert_slow(assert_data_structs());
    }
    assert(lineral_queue.empty() || !no_conflict());

    VERB(201, to_str());
    VERB(90, "GCP end");
    assert_slow(assert_data_structs());
};

// implementation of a dpll-solver
void solver::dpll_solve(stats &s) {
    VERB(25, "c dpll-solving start")
    // return UNSAT if linsys has no solution
    if (!no_conflict()) {
        s.sat = false;
        s.finished = true;
        return;
    }

    // current decision lvl
    dl = 0;
    dl_count[dl] = 1;

    // set update/fls/decH funcs
    dec_heu_t decH = &solver::dh_lex_LT;
    switch (opt.dh) {
    case dec_heu::vsids:
        decH = (opt.P.size()>0) ? &solver::dh_gp<&solver::dh_vsids> : &solver::dh_vsids;
        break;
    case dec_heu::lwl:
        decH = (opt.P.size()>0) ? &solver::dh_gp<&solver::dh_longest_wl> : &solver::dh_longest_wl;
        break;
    case dec_heu::lex:
        decH = (opt.P.size()>0) ? &solver::dh_gp<&solver::dh_lex_LT> : &solver::dh_lex_LT;
        break;
    case dec_heu::swl:
        decH = (opt.P.size()>0) ? &solver::dh_gp<&solver::dh_shortest_wl> : &solver::dh_shortest_wl;
        break;
    default:
        assert(false);
        break;
    }
    
    // stack for xsys that store alternative dec
    xsys new_xsys = xsys();
    std::stack<xlit> dec_stack;

    // GCP -- before making decisions!
    GCP(s);
    if( no_conflict() ) {
        if( find_implications_from_linerals(s) ) {
            goto dpll_gcp;
        }
    }

    while (true) {
        if (s.cancelled.load()) {
            VERB(10, "c cancelled");
            return;
        }
        if (active_cls > 0 || !no_conflict()) {
            // make decision / backtrack
            if (!no_conflict()) {
                dpll_conflict:
                VERB(25, "c " << std::to_string(dl) << " : "
                              << "conflict --> backtrack!")
                ++s.no_confl;
                // conflict!
                if (dl == 0) {
                    // return UNSAT
                    s.finished = true;
                    s.sat = false;
                    s.end = std::chrono::steady_clock::now();
                    
                    return;
                }

                ///// BACKTRACKING /////
                backtrack(dl-1);
                VERB(201, to_str());

                add_new_guess( std::move(dec_stack.top()) ); //add as 'guess', i.e., trail and reason stacks are ill-managed here, but that is irrelevant since we do not use those in the dpll-type solver!
                VERB(201, to_str());
                // decay + bump scores of conflict clause!
                //bump_score( dec_stack.top() );
                dec_stack.pop();
                //decay_score();
            } else {
                ++dl;
                ++dl_count[dl];
                trails.emplace_back( std::list<trail_elem>() );
                ++s.no_dec;
                // save active_cls count
                assert(active_cls == (var_t) std::count_if(xclss.begin(), xclss.end(), [&](const xcls_watch &xcls_w) { return xcls_w.is_active(dl_count) && xcls_w.is_irredundant(); }));
                active_cls_stack.emplace_back(active_cls);
                assert((var_t)active_cls_stack.size() == dl + 1);

                // make new decision!
                // use decisions heuristic to find next decision!
                xlit dec = (this->*decH)();
                VERB(50, "c " << std::to_string(dl) << " : "
                              << "decision " << std::to_string(s.no_dec) << " namely [" << dec.to_str() << "] or [" << dec.plus_one().to_str() << "]")
                //construct alt system
                dec_stack.emplace( dec.plus_one() );
                add_new_guess(std::move(dec));
            }

            dpll_gcp:
            GCP(s);
            //linear algebra on linerals
            if( need_linalg_inprocessing() ) {
                if( find_implications_from_linerals(s) ) {
                    //in case we did backtrack, fix dec_stack
                    while(dec_stack.size()>dl) dec_stack.pop();
                    goto dpll_gcp;
                }
            }


            assert((var_t)active_cls_stack.size() == dl + 1);
            assert((var_t)trails.size() == dl + 1);
            assert((var_t)dec_stack.size() == dl);
            assert(assert_data_structs());
        } else {
            //now active_cls == 0 AND no_conflict(); however the latter only means that alpha[0]!=bool3::True at the moment
            const auto [L,_] = get_assignments_xsys();
            if (!L.is_consistent()) {
                //enforce backtracking!
                lineral_watches[dl].emplace_back( xlit(0, false), alpha, alpha_dl, dl_count );
                add_implied_lineral(std::prev(lineral_watches[dl].end()), trail_t::GUESS);
            } else {
                solve_L(L, s);

                if(s.sols.size() < get_const_opts()->sol_count) {
                    //proceed as if we are at a conflict
                    goto dpll_conflict;
                }

                return;
            }
        }
    }

};

//implementation of a cdcl-solver
void solver::solve(stats &s) {
    if(opt.ca == ca_alg::no) return dpll_solve(s);
    VERB(25, "c cdcl-solving start")
    // return UNSAT if linsys has no solution
    if (!no_conflict()) {
        s.sat = false;
        s.finished = true;
        return;
    }

    // current decision lvl
    dl = 0;
    dl_count[dl] = 1;

    // set update/fls/decH funcs
    dec_heu_t decH = &solver::dh_lex_LT;
    switch (opt.dh) {
    case dec_heu::vsids:
        decH = (opt.P.size()>0) ? &solver::dh_gp<&solver::dh_vsids> : &solver::dh_vsids;
        break;
    case dec_heu::lwl:
        decH = (opt.P.size()>0) ? &solver::dh_gp<&solver::dh_longest_wl> : &solver::dh_longest_wl;
        break;
    case dec_heu::lex:
        decH = (opt.P.size()>0) ? &solver::dh_gp<&solver::dh_lex_LT> : &solver::dh_lex_LT;
        break;
    case dec_heu::swl:
        decH = (opt.P.size()>0) ? &solver::dh_gp<&solver::dh_shortest_wl> : &solver::dh_shortest_wl;
        break;
    default:
        assert(false);
        break;
    }
    
    ca_t analyze;
    switch (opt.ca) {
    case ca_alg::dpll:
        analyze = &solver::analyze_dpll;
        break;
    case ca_alg::fuip:
    case ca_alg::fuip_opt:
        analyze = &solver::analyze;
        break;
    default: //should never be executed
        assert(false);
        analyze = &solver::analyze_exp;
        break;
    }
    
    // stack for xsys that store alternative dec
    xsys new_xsys = xsys();

    // GCP -- before making decisions!
    GCP(s);
    if( no_conflict() ) {
        if( find_implications_from_linerals(s) ) {
            goto cdcl_gcp;
        }
    }

    while (true) {
        if (s.cancelled.load()) {
            VERB(10, "c cancelled");
            return;
        }
        if (active_cls > 0 || !no_conflict()) {
            // make decision / backtrack
            if (!no_conflict()) {
                VERB(25, "c " << std::to_string(dl) << " : "
                              << "conflict --> backtrack!")
                ++s.no_confl;
                ++confl_this_restart;
                // conflict!
                if (dl == 0) {
                    // return UNSAT
                    s.finished = true;
                    s.sat = false;
                    
                    return;
                }
            
                ///// BACKTRACKING /////
                ///// CLAUSE LEARNING /////
                auto [lvl, learnt_cls] = (this->*analyze)();
                // backtrack
                backtrack(lvl);
                VERB(201, to_str());

                // add learnt_cls
                add_learnt_cls( std::move(learnt_cls) );
                // decay score
                decay_score();

                VERB(201, to_str());
                //restart?
                if( need_restart() ) { restart(s); }
            } else {
                ++dl;
                ++dl_count[dl];
                trails.emplace_back( std::list<trail_elem>() );
                ++s.no_dec;
                // save active_cls count
                assert(active_cls == (var_t) std::count_if(xclss.begin(), xclss.end(), [&](const xcls_watch &xcls_w) { return xcls_w.is_active(dl_count) && xcls_w.is_irredundant(); }));
                active_cls_stack.emplace_back(active_cls);
                assert((var_t)active_cls_stack.size() == dl + 1);

                // make new decision!
                // use decisions heuristic to find next decision!
                xlit dec = (this->*decH)();
                VERB(50, "c " << std::to_string(dl) << " : "
                              << "decision " << std::to_string(s.no_dec) << " namely [" << dec.to_str() << "] or [" << dec.plus_one().to_str() << "]")
                add_new_guess( std::move(dec) );
            }

            cdcl_gcp:
            GCP(s);
            //linear algebra on linerals
            if( need_linalg_inprocessing() ) {
                if( find_implications_from_linerals(s) ) {
                    goto cdcl_gcp;
                }
            }

            assert((var_t)active_cls_stack.size() == dl + 1);
            assert((var_t)trails.size() == dl + 1);
            assert(assert_data_structs());
        } else {
            //now active_cls == 0 AND no_conflict(); however the latter only means that alpha[0]!=bool3::True at the moment
            auto [L,r_cls] = get_assignments_xsys();
            if (!L.is_consistent()) {
                backtrack( r_cls.get_assigning_lvl(alpha_dl) );
                add_learnt_cls( std::move(r_cls), false );
                GCP(s);
                if(no_conflict()) ++s.no_confl; //count as conflict here only if we do not need another conflict analysis
            } else {
                solve_L(L, s);

                if(s.sols.size() < get_const_opts()->sol_count && dl>0) {
                    //add clause that prevents this solution in the future, i.e., avoid taking the same decisions again
                    auto [lvl, learnt_cls] = analyze_dpll();
                    // backtrack
                    backtrack(lvl);
                    VERB(201, to_str());
                    // add learnt_cls
                    [[maybe_unused]] const var_t idx = add_learnt_cls( std::move(learnt_cls), false );
                    assert( idx>xclss.size() || xclss[idx].is_irredundant() );
                    // decay score
                    decay_score();

                    goto cdcl_gcp;
                }

                return;
            }
        }
    }
};


void solver::solve_L(const xsys& L, stats& s) const {
    //compute first sol
    s.sols.emplace_back( vec<bool>(get_num_vars(), false) );
    L.solve( s.sols.back() );
   
    s.sat = true;
    s.finished = true;

    if(s.sols.size()<opt.sol_count) {
        //print sol
        s.print_sol();
        VERB(0, "c solutions found so far: "+std::to_string(s.sols.size()));
    } else {
        return;
    }

    unsigned long long sol_ct = 1;
    vec<var_t> non_pivots; non_pivots.reserve( alpha.size()-L.size() );
    for(var_t idx=1; idx<alpha.size(); ++idx) {
        if(!L.get_pivot_poly_idx().contains(idx)) non_pivots.emplace_back(idx);
    }

    while(s.sols.size()<opt.sol_count && sol_ct < (unsigned long long) (1 << non_pivots.size()) ) {
        //compute next sol
        s.sols.emplace_back( vec<bool>(get_num_vars(), false) );
        for(var_t idx=0; idx<non_pivots.size(); ++idx) {
            s.sols.back()[ non_pivots[idx]-1 ] = (sol_ct >> idx) & 1;
        }
        //fix other positions
        L.solve( s.sols.back() );
        
        //print sol
        s.print_sol();
        VERB(0, "c solutions found so far: "+std::to_string(s.sols.size()));
        ++sol_ct;
    }
}


// overwrite to_str() func
std::string solver::to_str() const noexcept {
    // generate string of edges with lexicographic ordering!
    vec<std::string> str(xclss.size());
    // construct strings!
    auto to_str = [&](const xcls_watch &xcls) -> std::string { return xcls.to_str(); };
    std::transform(xclss.begin(), xclss.end(), str.begin(), to_str);
    std::sort(std::execution::par, str.begin(), str.end());

    std::stringstream ss;
    std::copy(str.begin(), str.end(), std::ostream_iterator<std::string>(ss, "; "));
    std::string result = ss.str();
    if (!result.empty()) {
        result.resize(result.length() - 1); // trim trailing space
    }

    return result;
}

std::string solver::to_xnf_str() const noexcept {
    auto xclss_str = vec<std::string>();
    var_t n_cls = 0;
    //add alpha
    VERB(80, "c printing alpha assignment")
    if (alpha[0] != bool3::None) {
        VERB(85, "instance is UNSAT; print only empty clause.")
        return "p xnf "+std::to_string(get_num_vars())+" 1\n 0\n";
    }
    for(var_t i=1; i<alpha.size(); ++i) {
        if(alpha[i] == bool3::None) continue;
        xclss_str.emplace_back( xlit(i, b3_to_bool(alpha[i])).to_xnf_str() + " 0" );
        ++n_cls;
        VERB(85, "c " + xclss_str.back());
    }
    VERB(80, "c printing linear polys")
    //add linear polys
    for(const auto& lw_dl : lineral_watches) {
        for(const auto& l : lw_dl) {
            if(!l.is_active(alpha)) continue;
            xlit lin = l.to_xlit();
            lin.reduce(alpha);
            if(lin.is_zero()) continue;
            xclss_str.emplace_back( lin.to_xnf_str() + " 0" );
            ++n_cls;
            VERB(85, "c " + xclss_str.back());
        }
    }
    VERB(80, "c printing XNF clauses")
    //go through xclss
    for(const auto& cls_w : xclss) {
        if(!cls_w.is_active(dl_count)) continue;
        std::string cls_str = "";
        auto cls = cls_w.to_xcls().reduced(alpha);
        for(const auto& lin : cls.get_ass_VS().get_xlits()) {
            cls_str += lin.plus_one().to_xnf_str();
            cls_str += " ";
        }
        xclss_str.emplace_back( cls_str + "0" );
        ++n_cls;
        VERB(95, "c " + xclss_str.back());
    }
    //convert to one big string
    std::string str = "p xnf "+std::to_string(get_num_vars())+" "+std::to_string(n_cls)+"\n";
    for(const auto &cls : xclss_str) {
        str += cls + "\n";
    }
    return str;
};

#ifdef NDEBUG
    bool solver::assert_data_structs() const noexcept { return true; };
#else
    bool solver::assert_data_structs() const noexcept {
        //ensure that dl_count[0] is {0,1} as soon as solving started
        assert( dl_count.size()==1 || dl_count[1]==0 || dl_count[0]==1 );
        
        //sanity check on alpha_dl
        for([[maybe_unused]] const auto lvl : alpha_dl) assert( lvl <= dl || lvl == (var_t) -1 );

        // check data structs of xclss
        for (var_t i = 0; i < xclss.size(); i++) {
            assert(xclss[i].assert_data_struct());
            //only check advanced conditions if lineral_queue is empty!
            if(no_conflict() && lineral_queue.empty()) assert(xclss[i].assert_data_struct(alpha, alpha_trail_pos, dl_count));
        }
        //check watch-lists
        {
            auto it = watch_list.begin();
            var_t idx = 0;
            while(it != watch_list.end()) {
                for([[maybe_unused]] auto i : *it) { assert( xclss[i].watches( idx ) ); }
                ++it; ++idx;
            }
        }
        {
            auto it = L_watch_list.begin();
            var_t idx = 0;
            while(it != L_watch_list.end()) {
                for([[maybe_unused]] auto [lvl, lin, dl_c] : *it) {
                    const auto& lin_w = *lin;
                    assert( dl_count[lvl]!=dl_c || lin_w.watches( idx ) || lin_w.to_xlit().is_one() || lin_w.to_xlit().is_zero() );
                }
                ++it; ++idx;
            }
        }

        //check that only assignemnts and alpha's backed by trail are assigned
        std::set<var_t> trail_inds;
        for(const auto& tr : trails) {
            for(const auto& t: tr) trail_inds.insert( t.ind );
        }
        var_t idx = 0;
        for(const auto& a : alpha) {
            if(a!=bool3::None) assert( trail_inds.contains( idx ) );
            ++idx;
        }
        
        //check active_cls -- on every dl!
        assert_slow( active_cls == (var_t) std::count_if(xclss.begin(), xclss.end(), [&](const xcls_watch& xcls) { return xcls.is_active(dl_count) && xcls.is_irredundant(); }) );
        auto dl_count_cpy = dl_count;
        for(var_t lvl = dl; lvl>0; --lvl) {
            ++dl_count_cpy[lvl];
            //VERB(90, "active_cls on lvl " + std::to_string(lvl) + ":   " + std::to_string(active_cls_stack[lvl]));
            //VERB(90, "active_cls recomputed on lvl " + std::to_string(lvl) + ": " + std::to_string(
            //    std::count_if(xclss.begin(), xclss.end(), [&](const xcls_watch &xcls) { return xcls.is_active(dl_count_cpy) && xcls.is_irredundant(); })
            //));
            assert_slow( !no_conflict() || active_cls_stack[lvl] == (var_t) 
                std::count_if(xclss.begin(), xclss.end(), [&](const xcls_watch& xcls) { return xcls.is_active(dl_count_cpy) && xcls.is_irredundant(); })
            );
        }


        //check trail
        for(var_t lvl = 0; lvl<dl; lvl++) {
            for(const auto& [ind, type, rs] : trails[lvl]) {
                assert( alpha[ind]==bool3::None || alpha_dl[ind]<=dl );
            }
        }
        for(const auto& [ind, type, rs] : trails[dl]) {
            assert( alpha[ind]==bool3::None || alpha_dl[ind]<=dl );
        }
        dl_c_t cnt = 1;
        for(var_t lvl=0; lvl<trails.size(); lvl++) {
            cnt += std::count_if(trails[lvl].begin(), trails[lvl].end(), [](const trail_elem& t) { return t.type==trail_t::IMPLIED_ALPHA; });
        }
        assert_slow( cnt == total_trail_length );

        //ensure that equiv_lits_dl is 'empty'
        if(!opt.eq) for(const auto& lvl : equiv_lits_dl) assert(lvl==(var_t)-1);

        // check solution! (for rand-10-20.xnf) -- may help in debugging!
        /*
        if (opt.num_vars == 10) {
            vec<bool> sol = {false, false, true, false, false, false, false, true, false, true};
            std::cout << "NO SOL for xclss idxs ";
            for (var_t i = 0; i < xclss.size(); ++i) {
                if (!xclss[i].eval(sol)) {
                    std::cout << std::to_string(i) << " ";
                }
            }
            std::cout << std::endl;
            std::cout << "NO SOL for assignment idxs ";
            for (var_t i = 0; i < assignments.size(); ++i) {
                if (!assignments[i].eval(sol)) {
                    std::cout << std::to_string(i) << " ";
                }
            }
            std::cout << std::endl;
        }
        */
        return true;
    };
#endif



void solver::print_trail(std::string lead) const noexcept {
  VERB(80, lead);
  VERB(80, lead+" trail");
  VERB(80, lead+" dl pos type unit");

  const auto to_string = [](var_t i, var_t width) {
    std::stringstream ss;
    ss.width(width);
    ss << std::left << i;
    return ss.str();
  };
  
  const auto trail_t_to_str = [](const trail_t& t) -> std::string {
    switch(t) {
      case trail_t::EQUIV:         return "EQUIV ";
      case trail_t::IMPLIED_UNIT:  return "UNIT  ";
      case trail_t::IMPLIED_ALPHA: return BOLD("ALPHA ");
      case trail_t::GUESS:         return BOLD("GUESS ");
    }
    return "";
  };

  var_t w = std::to_string(alpha.size()).length();

  var_t lvl = 0;
  for(const auto& t_dl : trails) {
    var_t i = 0;
    VERB(80, lead+" " + to_string(i,w));
    for (const auto& t : t_dl) {
        assert( (t.type!=trail_t::IMPLIED_ALPHA) || alpha_dl[t.ind] == lvl );
        if(t.type==trail_t::IMPLIED_UNIT) {
            VERB(80, lead+" " + to_string(lvl,w) + " " + to_string(i,w) + " " + trail_t_to_str(t.type) + " " + "x" + to_string(t.ind,w) + " " + " from " + get_reason(t).to_str() );
        } else {
            VERB(80, lead+" " + to_string(lvl,w) + " " + to_string(i,w) + " " + trail_t_to_str(t.type) + " " + "x" + to_string(t.ind,w) + " " + " from " + t.lin->to_str());
        }
        ++i;
    }
    ++lvl;
  }
}