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
    
    lineral_watches = vec<vec<xlit_watch>>(num_vars+1, vec<xlit_watch>() );
    
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
    last_phase = vec<bool3>(num_vars + 1, bool3::None);
    //init last_phase according to init_phase of reordering:
    for(var_t idx=0; idx<opt_.P.size(); ++idx) {
        last_phase[idx+1] = to_bool3( opt_.P.get_phase(idx) );
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
        } else if (cls.is_zero()) {
            //ignore cls
        } else {
            _xclss.emplace_back( std::move(cls) );
        }
    }
    //reduce xclss with _L
    xsys _Lsys(_L);
    for(auto& cls : _xclss) {
        cls.update_short(_Lsys); //TODO no full reduction?!
        init_and_add_xcls_watch( std::move(cls), false );
    }

    assert(active_cls == xclss.size());

    //init xlits
    for(const auto& [_,it] : _Lsys.get_pivot_poly_idx()) queue_implied_lineral(*it, -1);

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
    ///// --------------- /////
    if (dl - lvl > 1) VERB(80, "c " << std::to_string(dl) << " : BACKJUMPING BY MORE THAN ON LEVEL!");
    // update dl_count
    for(var_t dl_ = dl; dl_>lvl; dl_--) dl_count[dl_]++;
    ///// --------------- /////

    // trail and assignments!
  #ifndef NDEBUG
    print_trail();
    print_assignments();
  #endif

    //undo unit linerals, revert assignments and alpha, and reset trail, reasons, queue
    while(dl>lvl) {
        while(!TRAIL.empty()) { pop_trail(); };
        trails.pop_back();
        assert(lineral_watches[dl].empty());
        //adapt dl
        --dl;
        //restore active_cls count
        active_cls = active_cls_stack.back();
        active_cls_stack.pop_back();
    }
    assert(dl==lvl);

    // check active_cls count
    //VERB(90, "active_cls restored:   " + std::to_string(active_cls))
    //VERB(90, "active_cls recomputed: " + std::to_string(std::count_if(xclss.begin(), xclss.end(), [&](const xcls_watch &xcls_w) { return xcls_w.is_active(dl_count) && xcls_w.is_irredundant(); })))
    assert(active_cls == (var_t) std::count_if(xclss.begin(), xclss.end(), [&](const xcls_watch &xcls_w) { return xcls_w.is_active(dl_count) && xcls_w.is_irredundant(); }));
    // revert assignments_xsys

    //cleanup lineral_queue
    lineral_queue.clear();

  #ifndef NDEBUG
    print_trail();
    print_assignments();
  #endif

    VERB(201, to_str());
    VERB(90, "BACKTRACK end");
    assert(assert_data_structs());
};

// decision heuristics
std::pair<xsys, xsys> solver::dh_vsids() {
    assert(!order_heap_vsids.empty());
    var_t ind = 0;
    while (ind==0 || (alpha[ind] != bool3::None && !order_heap_vsids.empty() )) {
        ind = order_heap_vsids.removeMin();
    }
    xlit xi = xlit( ind, last_phase[ind]==bool3::True);
    return std::pair<xsys, xsys>(xsys(xi), xsys(xi.plus_one()));

    //var_t lt_max = 0;
    //unsigned int max_activity = 0;
    //for(size_t idx=1; idx<alpha.size(); ++idx) {
    //    if(alpha[idx]==bool3::None && (activity_score[idx] > max_activity)) {
    //        lt_max = idx; max_activity = activity_score[idx];
    //    }
    //}
    //assert(lt_max!=0 && lt_max < (var_t)alpha.size());

    //xlit xi = xlit( lt_max, last_phase[lt_max]==bool3::True);
    //return std::pair<xsys, xsys>(xsys(xi), xsys(xi.plus_one()));
};

std::pair<xsys, xsys> solver::dh_shortest_wl() {
    //find unassigned variable that has the longest watch_list
    var_t lt_min = 0;
    size_t size_min = xclss.size() + 1;
    for(size_t idx=1; idx<watch_list.size(); ++idx) {
        if(alpha[idx]==bool3::None && (watch_list[idx].size() < size_min)) {
            lt_min = idx; size_min = watch_list[idx].size();
        }
    }
    assert(lt_min!=0 && lt_min < (var_t)alpha.size());

    xlit xi = xlit( lt_min, last_phase[lt_min]==bool3::True);
    return std::pair<xsys, xsys>(xsys(xi), xsys(xi.plus_one()));
}

std::pair<xsys, xsys> solver::dh_longest_wl() {
    //find unassigned variable that has the longest watch_list
    var_t lt_max = 0;
    size_t size_max = 0;
    for(size_t idx=1; idx<watch_list.size(); ++idx) {
        if(alpha[idx]==bool3::None && (watch_list[idx].size() > size_max)) {
            lt_max = idx; size_max = watch_list[idx].size();
        }
    }
    assert(lt_max!=0 && lt_max < (var_t)alpha.size());

    xlit xi = xlit( lt_max, last_phase[lt_max]==bool3::True);
    return std::pair<xsys, xsys>(xsys(xi), xsys(xi.plus_one()));
}

std::pair<xsys, xsys> solver::dh_lex_LT() {
    var_t i = 1;
    while(alpha[i] != bool3::None) ++i;
    assert(i<alpha.size());
    //xlit xi = xlit( std::move( vec<var_t>({i}) ), (last_phase[i]==bool3::True), true );
    xlit xi = xlit( i, last_phase[i]==bool3::True);
    //xlit xi = xlit( (last_phase[i]==bool3::True) ? vec<var_t>({0,i}) : vec<var_t>({i}) );
    //xlit xi = xlit( vec<var_t>({i}) );
    return std::pair<xsys, xsys>(xsys(xi), xsys(xi.plus_one()));
    //return std::pair<xsys, xsys>(xsys(xi.plus_one()), xsys(xi));
};


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

xcls solver::get_last_reason() const {
    vec<xlit> lits = vec<xlit>();
    // if the reason cls of the last learnt unit is 'out of range', i.e., last trail entry comes from guess, return empty reason-cls
    if (lineral_watches[dl].back().get_reason() >= xclss.size()) {
        lits.push_back( xlit(vec<var_t>({0})) );
        return xcls(lits);
    }
    const xcls_watch &cls = xclss[ lineral_watches[dl].back().get_reason() ];
    assert(cls.is_unit(dl_count));
    return cls.to_xcls();
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
    xcls_watch learnt_cls = (trails.back().back().type == trail_t::LINERAL_IMPLIED_ALPHA || trails.back().back().type == trail_t::LEARNT_UNIT) ? xcls_watch( lineral_watches[0][trails.back().back().rs_cls_idx], alpha_dl ) : xclss[ trails.back().back().rs_cls_idx ];
    assert(learnt_cls.is_unit(dl_count));
    VERB(70, "   * reason clause " + learnt_cls.to_str() + " for UNIT " + learnt_cls.get_unit().to_str() );
    bump_score( TRAIL.back().ind );
    pop_trail(); //remove conflict from trail, i.e., now we should have alpha[0]==bool3:None
    
    //as long as assigning_lvl is dl OR -1 (i.e. equiv-lits are used!), resolve with reason clauses
    while( learnt_cls.get_assigning_lvl() == dl || learnt_cls.get_assigning_lvl() == (var_t) -1 ) {
        assert(!TRAIL.empty());
        VERB(70, "   * conflict clause is " + learnt_cls.to_str());
        VERB(70, "   '----> gives with current assignments: " + learnt_cls.to_xcls().reduced(alpha).to_str());

        unit = std::move(learnt_cls.get_unit());
        unit.reduce(alpha);
        unit.reduce(equiv_lits, equiv_lits_dl, 0, alpha);
        //if unit is still not 1, we need to resolve with reason clauses for equiv_lits which must reduce unit to 1 (!)
      #ifdef USE_EQUIV
        if(!unit.is_one()) {
            //note: unit MUST reduce to 1 under equiv_lits
          #ifndef NDEBUG
            xlit unit_cpy = unit;
            unit_cpy.reduce(equiv_lits);
            unit_cpy.reduce(alpha);
            assert(unit_cpy.is_one());
          #endif
            const auto reason_cls = xclss[equiv_lits[unit.LT()].reason];
            VERB(70, "   * reason clause " + reason_cls.to_str() + " for EQUIVALENCE " + equiv_lits[unit.LT()].to_str(unit.LT()) );
            //resolve!
            learnt_cls.resolve( reason_cls, alpha, alpha_dl, alpha_trail_pos, dl_count, equiv_lits, equiv_lits_dl);
            continue;
        }
      #else
        assert( unit.is_one() );
      #endif
        assert(!learnt_cls.to_xcls().is_zero());

        //pop trail until we are at the implied alpha that is watched by learnt_cls (by wl1)
        while( (TRAIL.back().type != trail_t::IMPLIED_ALPHA && TRAIL.back().type != trail_t::LINERAL_IMPLIED_ALPHA && TRAIL.back().type != trail_t::LEARNT_UNIT ) || !learnt_cls.unit_contains(TRAIL.back().ind) ) {
            pop_trail();
        }
        
        //special case: TRAIL.back().type == trail_t::LINERAL_IMPLIED_ALPHA, which occurs only if the reason for the implied alpha is a unit clause, i.e., a lineral at dl 0:
        if( TRAIL.back().type == trail_t::LINERAL_IMPLIED_ALPHA || TRAIL.back().type == trail_t::LEARNT_UNIT) {
            assert(TRAIL.back().rs_cls_idx < lineral_watches[0].size());
            VERB(70, "   * reason clause " + lineral_watches[0][TRAIL.back().rs_cls_idx].to_str() );
            const xlit& lin = lineral_watches[0][TRAIL.back().rs_cls_idx];
            bump_score( TRAIL.back().ind );
            pop_trail();
            
            learnt_cls.add_to_unit( lin, alpha, alpha_dl, alpha_trail_pos, dl_count, equiv_lits, equiv_lits_dl );
            continue;
        }
        
        //get reason_cls
        assert(TRAIL.back().rs_cls_idx < xclss.size() && TRAIL.back().type == trail_t::IMPLIED_ALPHA);
        const auto& reason_cls = xclss[TRAIL.back().rs_cls_idx];
        VERB(70, "   * reason clause " + reason_cls.to_str() + " for UNIT " + reason_cls.get_unit().to_str() );
    #ifndef NDEBUG
        //ensure that reason cls is reason for provided alpha
        xlit unit = reason_cls.get_unit();
        unit.reduce(alpha);
        unit.reduce(equiv_lits, equiv_lits_dl, 0, alpha);
        assert(unit.is_zero()); //unit MUST reduce to zero, as TRAIL is not yet popped
    #endif
        bump_score( TRAIL.back().ind );
        pop_trail(); //remove from trail!

        learnt_cls.resolve( reason_cls, alpha, alpha_dl, alpha_trail_pos, dl_count, equiv_lits, equiv_lits_dl);
    }
    // clean-up trail!
    
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
    const var_t b_lvl = learnt_cls.get_assigning_lvl();
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
    xcls_watch learnt_cls = (trails.back().back().type == trail_t::LINERAL_IMPLIED_ALPHA || trails.back().back().type == trail_t::LEARNT_UNIT) ? xcls_watch( lineral_watches[0][trails.back().back().rs_cls_idx], alpha_dl ) : xclss[ trails.back().back().rs_cls_idx ];
    assert(learnt_cls.is_unit(dl_count));
    VERB(70, "   * reason clause is   " + BOLD( learnt_cls.to_str() ) + " for UNIT " + learnt_cls.get_unit().to_str() );
    bump_score( TRAIL.back().ind );
    pop_trail(); //remove conflict from trail, i.e., now we should have alpha[0]==bool3:None

    //as long as assigning_lvl is dl OR -1 (i.e. equiv-lits are used!), resolve with reason clauses
    while( learnt_cls.get_assigning_lvl() == dl || learnt_cls.get_assigning_lvl() == (var_t) -1 ) {
        assert(!TRAIL.empty());
        VERB(70, "   * conflict clause is " + BOLD( learnt_cls.to_str() ) + "   --> gives with current assignments: " + learnt_cls.to_xcls().reduced(alpha).to_str());

        unit = std::move(learnt_cls.get_unit());
        unit.reduce(alpha);
        unit.reduce(equiv_lits, equiv_lits_dl, 0, alpha);
        //if unit is still not 1, we need to resolve with reason clauses for equiv_lits which must reduce unit to 1 (!)
      #ifdef USE_EQUIV
        if(!unit.is_one()) {
            //note: unit MUST reduce to 1 under equiv_lits
          #ifndef NDEBUG
            xlit unit_cpy = unit;
            unit_cpy.reduce(equiv_lits);
            unit_cpy.reduce(alpha);
            assert(unit_cpy.is_one());
          #endif
            const auto reason_cls = xclss[equiv_lits[unit.LT()].reason];
            VERB(70, "   * reason clause is   " + reason_cls.to_str() + " for EQUIVALENCE " + equiv_lits[unit.LT()].to_str(unit.LT()) );
            //resolve!
            learnt_cls.resolve( reason_cls, alpha, alpha_dl, alpha_trail_pos, dl_count, equiv_lits, equiv_lits_dl, opt.ca == ca_alg::fuip_opt );
            continue;
        }
      #else
        assert( unit.is_one() );
      #endif
        assert(!learnt_cls.to_xcls().is_zero());

        //pop trail until we are at the implied alpha that is watched by learnt_cls (by wl1)
        while( (TRAIL.back().type != trail_t::IMPLIED_ALPHA && TRAIL.back().type != trail_t::LINERAL_IMPLIED_ALPHA && TRAIL.back().type != trail_t::LEARNT_UNIT ) || !learnt_cls.unit_contains(TRAIL.back().ind) ) {
            assert(!TRAIL.empty());
            pop_trail();
        }
        
        //special case: TRAIL.back().type == trail_t::LINERAL_IMPLIED_ALPHA, which occurs only if the reason for the implied alpha is a unit clause, i.e., a lineral at dl 0:
        if( TRAIL.back().type == trail_t::LINERAL_IMPLIED_ALPHA || TRAIL.back().type == trail_t::LEARNT_UNIT) {
            assert(TRAIL.back().rs_cls_idx < lineral_watches[0].size());
            VERB(70, "   * reason clause is   " + BOLD( lineral_watches[0][TRAIL.back().rs_cls_idx].to_str() ) );
            const xlit& lin = lineral_watches[0][TRAIL.back().rs_cls_idx];
            bump_score( TRAIL.back().ind );
            pop_trail();
            
            learnt_cls.add_to_unit( lin, alpha, alpha_dl, alpha_trail_pos, dl_count, equiv_lits, equiv_lits_dl );
            continue;
        }
        
        //get reason_cls
        assert(TRAIL.back().rs_cls_idx < xclss.size() && TRAIL.back().type == trail_t::IMPLIED_ALPHA);
        const auto reason_cls = xclss[TRAIL.back().rs_cls_idx];
        VERB(70, "   * reason clause is   " + BOLD( reason_cls.to_str() ) + " for UNIT " + reason_cls.get_unit().to_str() );
    #ifndef NDEBUG
        //ensure that reason cls is reason for provided alpha
        xlit unit = reason_cls.get_unit();
        unit.reduce(alpha);
        unit.reduce(equiv_lits, equiv_lits_dl, 0, alpha);
        assert(unit.is_zero()); //unit MUST reduce to zero, as TRAIL is not yet popped
    #endif
        bump_score( TRAIL.back().ind );
        pop_trail(); //remove from trail!

        learnt_cls.resolve( reason_cls, alpha, alpha_dl, alpha_trail_pos, dl_count, equiv_lits, equiv_lits_dl, opt.ca == ca_alg::fuip_opt);
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
    const var_t b_lvl = learnt_cls.get_assigning_lvl();
    if( dl < learnt_cls.size() && b_lvl == dl-1 ) {
        VERB(50, "   * negated decisions lead to smaller learnt_cls and the same backtrack-level!");
        //assert(false);
        
    }
    
    VERB(70, "****");
    return std::pair<var_t, xcls_watch>(b_lvl, learnt_cls);
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
    assert( assert_data_structs() );
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
    //empty watchlists
    for(auto& wl : watch_list) wl.clear();
    //re-fill watchlists!
    for(var_t i=0; i<xclss.size(); ++i) {
        watch_list[xclss[i].get_wl0()].emplace_back( i );
        watch_list[xclss[i].get_wl1()].emplace_back( i );
    }
    assert( assert_data_structs() );
    
    VERB(50, "c removing " + std::to_string( (double) (no_cls / xclss.size()) ) + "\% clauses.")

    update_restart_schedule(s.no_restarts);
    VERB(90, "c restart done")
};

void solver::remove_fixed_alpha(const var_t upd_lt) {
    VERB(90, "remove_fixed_alpha start" );
    VERB(90, to_str());
    assert( alpha[upd_lt]!=bool3::None && alpha_dl[upd_lt]==0 );
    const bool3 val = alpha[upd_lt];
    //rm upd_lt from lineral_watches[0] (all other levels are empty!)
    for(auto& lin_watch : lineral_watches[0]) {
        if(lin_watch.is_active(dl_count) && !lin_watch.watches(upd_lt)) {
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
    VERB(90, "remove_fixed_alpha end" );
    VERB(90, to_str());
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
          const auto [lvl, i, dl_, dl_c] = *it;
          //if assignments_watch[i] has been removed and possibly filled with another literal between adding it to this watch-list in the first place, we have to fix the watching scheme now!
          if(i>=lineral_watches[lvl].size() || dl_count[dl_] != dl_c) {
              it = L_watch_list[upd_lt].erase( it );
              continue;
          }
          assert(lineral_watches[lvl][i].watches(upd_lt));
          //skip if it is already assigned && it does not contradict alpha[i]
          //TODO optimize! i.e., offer a function that checks if it is was already assigned the last time it was checked! (use dl_count?!)
          const auto& [lt,val] = lineral_watches[lvl][i].get_assignment(alpha);
          if(val!=bool3::None && alpha[lt] == val) {
            ++it;
            continue;
          }
          const auto& [new_wl, ret] = lineral_watches[lvl][i].update(upd_lt, alpha);
          //if watched-literal has changed, i.e., new_wl != 0; update watch-list
          if(new_wl != upd_lt) {
              //rm *it from current watch-list:
              it = L_watch_list[upd_lt].erase( it );
              //add i to newly watched literal:
              L_watch_list[new_wl].push_back({lvl, i, dl_, dl_c});
          } else {
              ++it;
          }
          switch (ret) {
          case xlit_upd_ret::ASSIGNING:
            {
              assert( lineral_watches[lvl][i].is_assigning(alpha) );
              // update alpha
              const auto [lt,val] = lineral_watches[lvl][i].get_assignment(alpha);
              assert(alpha[lt] == bool3::None);
              const var_t rs = lineral_watches[lvl][i].get_reason();
              assert( rs < xclss.size() || lvl == 0 );
              queue_implied_alpha(lt, val, rs < xclss.size() ? rs : i, rs < xclss.size() ? trail_t::IMPLIED_ALPHA : trail_t::LINERAL_IMPLIED_ALPHA);
            }
            break;
          case xlit_upd_ret::UNIT:
              assert(!lineral_watches[lvl][i].is_assigning(alpha));
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
            //is_active can only be used AFTER update! -- instead of is_active check if update has been performed by checking if upd_lt is watched
            assert(xclss[i].watches(upd_lt));
            if(!xclss[i].is_active(dl_count)) { ++it; continue; }
            const auto& [new_wl, ret] = xclss[i].update(upd_lt, alpha, alpha_dl, dl_count);
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
                // add to assignments
                if( queue_implied_lineral(new_unit, i) ) {
                    ++s.new_px_upd;
                }
                //if (!no_conflict()) { 
                //    VERB(70, "UNSAT with conflict clause " + get_last_reason().to_str()); 
                //    return; //quit propagation immediately at conflict!
                //}
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
    }
    assert(lineral_queue.empty() || !no_conflict());

    VERB(201, to_str());
    VERB(90, "GCP end");
    assert(assert_data_structs());
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
        decH = &solver::dh_vsids;
        break;
    case dec_heu::lwl:
        decH = &solver::dh_longest_wl;
        break;
    case dec_heu::lex:
        decH = &solver::dh_lex_LT;
        break;
    case dec_heu::swl:
        decH = &solver::dh_shortest_wl;
        break;
    default:
        assert(false);
        break;
    }
    
    // stack for xsys that store alternative dec
    xsys new_xsys = xsys();
    std::stack<xsys> dec_stack;

    // GCP -- before making decisions!
    GCP(s);
    if( no_conflict() && need_linalg_inprocessing() ) {
        ++s.no_linalg;
        auto r_clss = find_implied_alpha_from_linerals();
        for(auto& r_cls : r_clss) {
            ++s.no_linalg_prop;
            assert(r_cls.get_assigning_lvl() == dl);
            add_learnt_cls( std::move(r_cls), false);
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

                add_new_guess( dec_stack.top() ); //add as 'guess', i.e., trail and reason stacks are ill-managed here, but that is irrelevant since we do not use those in the dpll-type solver!
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
                active_cls_stack.emplace_back(active_cls);
                assert((var_t)active_cls_stack.size() == dl + 1);

                // make new decision!
                // use decisions heuristic to find next decision!
                std::pair<xsys, xsys> dec = (this->*decH)();
                VERB(25, "c " << std::to_string(dl) << " : "
                              << "decision " << std::to_string(s.no_dec) << " : " << std::to_string(dec.first.size()) << " or " << std::to_string(dec.second.size()) << " eqs")
                VERB(50, "c " << std::to_string(dl) << " : "
                              << "decision " << std::to_string(s.no_dec) << " namely [" << dec.first.to_str() << "] or [" << dec.second.to_str() << "]")
                add_new_guess(std::move(dec.first));
                //construct alt system
                dec_stack.emplace( std::move(dec.second) );
            }

            dpll_gcp:
            GCP(s);
            //linear algebra on linerals
            if( no_conflict() && need_linalg_inprocessing() ) {
                ++s.no_linalg;
                auto r_clss = find_implied_alpha_from_linerals();
                for(auto& r_cls : r_clss) {
                    ++s.no_linalg_prop;
                    if(r_cls.get_assigning_lvl() < dl) {
                        backtrack( r_cls.get_assigning_lvl() );
                        add_new_guess( r_cls.get_unit() ); //add as 'guess', i.e., trail and reason stacks are ill-managed here, but that is irrelevant since we do not use those in the dpll-type solver!
                        while(dec_stack.size()>dl) dec_stack.pop();
                        goto dpll_gcp;
                    }
                    add_new_guess( r_cls.get_unit() ); //add as 'guess', i.e., trail and reason stacks are ill-managed here, but that is irrelevant since we do not use those in the dpll-type solver!
                }
                if(!r_clss.empty()) {
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
                add_implied_lineral(xlit(0, false), -1);
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
        decH = &solver::dh_vsids;
        break;
    case dec_heu::lwl:
        decH = &solver::dh_longest_wl;
        break;
    case dec_heu::lex:
        decH = &solver::dh_lex_LT;
        break;
    case dec_heu::swl:
        decH = &solver::dh_shortest_wl;
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
    if( no_conflict() && need_linalg_inprocessing() ) {
        ++s.no_linalg;
        auto r_clss = find_implied_alpha_from_linerals();
        for(auto& r_cls : r_clss) {
            ++s.no_linalg_prop;
            assert(r_cls.get_assigning_lvl() == dl);
            add_learnt_cls( std::move(r_cls), false);
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
                active_cls_stack.emplace_back(active_cls);
                assert((var_t)active_cls_stack.size() == dl + 1);

                // make new decision!
                // use decisions heuristic to find next decision!
                std::pair<xsys, xsys> dec = (this->*decH)();
                VERB(25, "c " << std::to_string(dl) << " : "
                              << "decision " << std::to_string(s.no_dec) << " : " << std::to_string(dec.first.size()) << " or " << std::to_string(dec.second.size()) << " eqs")
                VERB(50, "c " << std::to_string(dl) << " : "
                              << "decision " << std::to_string(s.no_dec) << " namely [" << dec.first.to_str() << "] or [" << dec.second.to_str() << "]")
                add_new_guess(std::move(dec.first));
            }

            cdcl_gcp:
            GCP(s);
            //linear algebra on linerals
            if( no_conflict() && need_linalg_inprocessing() ) {
                ++s.no_linalg;
                auto r_clss = find_implied_alpha_from_linerals();
                for(auto& r_cls : r_clss) {
                    ++s.no_linalg_prop;
                    if(r_cls.get_assigning_lvl() < dl) {
                        backtrack( r_cls.get_assigning_lvl() );
                        add_learnt_cls( std::move(r_cls), false);
                        goto cdcl_gcp;
                    }
                    add_learnt_cls( std::move(r_cls), false);
                }
                if(!r_clss.empty()) {
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
                backtrack( r_cls.get_assigning_lvl() );
                add_learnt_cls( std::move(r_cls), false );
                GCP(s);
                if(no_conflict()) ++s.no_confl; //count as conflict here only if we do not need another conflict analysis
            } else {
                solve_L(L, s);

                if(s.sols.size() < get_const_opts()->sol_count) {
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
        s.print_sol(get_const_opts()->P);
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
        s.print_sol(get_const_opts()->P);
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
            if(!l.is_active(dl_count)) continue;
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
        //sanity check on assignments_dl
        
        for([[maybe_unused]] const auto lvl : alpha_dl) assert( lvl <= dl || lvl == (var_t) -1 );

        // check data structs of xclss
        for (var_t i = 0; i < xclss.size(); i++) {
            assert(xclss[i].assert_data_struct());
            //only check advanced conditions if lineral_queue is empty!
            if(no_conflict() && lineral_queue.empty()) assert(xclss[i].assert_data_struct(alpha,dl_count));
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
                for([[maybe_unused]] auto [lvl, i, dl_, dl_c] : *it) {
                    assert( i>=lineral_watches[lvl].size() || dl_count[dl_]!=dl_c || lineral_watches[lvl][i].watches( idx ) || lineral_watches[lvl][i].to_xlit().is_one() || lineral_watches[lvl][i].to_xlit().is_zero() );
                    assert( lvl == dl_ );
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
        
        //check active_cls
        assert( active_cls == (var_t) std::count_if(xclss.begin(), xclss.end(), [&](const xcls_watch& xcls) { return xcls.is_active(dl_count) && xcls.is_irredundant(); }) );

        //check that trails[dl] contains exactly as many trail_t::IMPLIED_UNIT elements as there are xlit_watches in lineral_watches[dl]
        for(var_t lvl = 0; lvl<=dl; lvl++) {
            assert( (var_t) std::count_if(trails[lvl].begin(), trails[lvl].end(), [&](const trail_elem& t) { return t.type==trail_t::IMPLIED_UNIT || t.type==trail_t::GUESS; }) == (var_t) lineral_watches[lvl].size() );
            for(const auto& [ind, type, rs] : trails[lvl]) {
                assert( alpha[ind]==bool3::None || alpha_dl[ind]<=dl );
            }
        }

      #ifndef USE_EQUIV
        //ensure that equiv_lits_dl is 'empty'
        for(const auto& lvl : equiv_lits_dl) assert(lvl==(var_t)-1);
      #endif

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
  VERB(80, lead+" pos dl type unit");

  const auto trail_t_to_str = [](const trail_t& t) {
    switch(t) {
      case trail_t::EQUIV:                 return "NEW_EQUIV ";
      case trail_t::IMPLIED_UNIT:          return "IMPL_UNIT ";
      case trail_t::LINERAL_IMPLIED_ALPHA: return "IMPL_ALPHA";
      case trail_t::IMPLIED_ALPHA:         return "IMPL_ALPHA";
      case trail_t::GUESS:                 return "GUESS     ";
      case trail_t::LEARNT_UNIT:           return "LRNT_UNIT ";
    }
    return "";
  };
  var_t lvl = 0;
  for(const auto& t_dl : trails) {
    var_t i = 0;
    for (const auto& t : t_dl) {
        assert( (t.type!=trail_t::IMPLIED_ALPHA && t.type!=trail_t::LINERAL_IMPLIED_ALPHA) || alpha_dl[t.ind] == lvl );
        VERB(80, lead+" " + std::to_string(i) + " " + std::to_string(lvl) + " " + trail_t_to_str(t.type) + " " + "x" + std::to_string(t.ind) + " " + b3_to_str( alpha[t.ind] ));
        ++i;
    }
    ++lvl;
  }
}