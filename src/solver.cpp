#include <iostream>
#include <stack>
#include <deque>
#include <set>
#include <queue>
#include <m4ri/m4ri.h>

#include "solver.hpp"


std::ostream& operator<<(std::ostream& os, const trail_t& t) {
    switch (t) {
        case trail_t::GUESS: os << BOLD("GUESS "); break;
        case trail_t::ALPHA: os << BOLD("ALPHA "); break;
        case trail_t::EQUIV: os << "EQUIV "; break;
        case trail_t::UNIT:  os << "UNIT  "; break;
    }
    return os;
}

std::ostream& operator<<(std::ostream& os, const queue_t& t) {
    switch (t) {
        case queue_t::NEW_GUESS:     os << BOLD("GUESS "); break;
        case queue_t::IMPLIED_ALPHA: os << BOLD("ALPHA "); break;
        case queue_t::NEW_UNIT:      os << BOLD("UNIT  "); break;
    }
    return os;
}

std::ostream& operator<<(std::ostream& os, const origin_t& t) {
    switch (t) {
        case origin_t::CLAUSE:  os << "(CLS)  "; break;
        case origin_t::GUESS:   os << "(DEC)  "; break;
        case origin_t::IG:      os << "(IG)   "; break;
        case origin_t::INIT:    os << "(INIT) "; break;
        case origin_t::LGJ:     os << "(LGJ)  "; break;
        case origin_t::LINERAL: os << "(LIN)  "; break;
    }
    return os;
}

solver::solver(const vec< vec<lineral> >& clss, const var_t num_vars, const options& opt_) noexcept : opt(opt_), IG(clss, xornado::options(num_vars, xornado::fls_alg::full, xornado::constr::extended, opt.pp, opt.verb)) {
    vec< cls > clss_; clss_.reserve(clss.size());
    for(const auto& cls : clss) {
        clss_.emplace_back( cls );
    }

    #ifndef NDEBUG
        if(opt.verb==0) opt.verb = 100;
    #endif

    //init watch_list
    watch_list.resize(num_vars+1);
    L_watch_list.resize(num_vars+1);
    lineral_watches = vec<list<lineral_watch>>(num_vars+1, list<lineral_watch>() );
    
    // init assignments
    alpha = vec<bool3>(num_vars + 1, bool3::None);
    alpha_dl = vec<var_t>(num_vars + 1, (var_t) -1);
    alpha_trail_pos = vec<var_t>(num_vars + 1, (var_t) -1);
    alpha_lin = vec<lin_w_it>(num_vars + 1);
    equiv_lits = vec<equivalence>(num_vars+1);
    dl_count = vec<dl_c_t>(num_vars+1, 1); 
    trails = vec< list<trail_elem> >();
    trails.reserve(num_vars+1);
    trails.emplace_back( list<trail_elem>() );
    stepwise_lit_trail_length = 1;
    last_phase = vec<bool3>(num_vars + 1, bool3::None);
    //init last_phase according to init_phase of guessing_path:
    for(var_t idx=0; idx<opt.P.size(); ++idx) {
        last_phase[opt.P[idx]] = to_bool3( opt.P.get_phase(idx) );
    }

    init_clss(clss_);
    
    //init order_heap and activity_score
    activity_score = vec<double>(num_vars + 1, 1);
    for (var_t i = 0; i < num_vars+1; i++) {
        activity_score[i] += watch_list[i].size();
    }
    for(var_t i = 1; i<=num_vars; ++i) {
        order_heap_vsids.insert( i );
    }

    //init params
    init_cleaning_params();
    update_restart_schedule(0);

    //prepare IG
    xornado::options xopt = xornado::options(num_vars, clss.size());
    xopt.verb = opt.verb;
    xopt.ext = xornado::constr::simple;
}

void solver::init_clss(const vec< cls >& clss) noexcept {
    xnf_clss.reserve(2 * clss.size());

    // temporarily store clss in _clss - before init of xclss we might want to reduce with pure literals in _L (!)
    list<cls> _clss;
    list<lineral> Lsys_lins;

    // run through XNF clauses to find lineq
    for(const auto& cls : clss) {
        if(cls.is_zero()) continue;
        //check if clause reduces to unit
        if (cls.deg() == 1 || cls.is_one()) { // lin-eq!
            Lsys_lins.emplace_back( std::move(cls.get_unit()) );
        } else {
            _clss.emplace_back( cls );
        }
    }

    // linsys of literals
    lin_sys _Lsys( std::move(Lsys_lins) );

    //reduce clss with _L
    if(opt.ip==initial_prop_opt::nbu) {
        //reduce all cls
        restart:
        for(auto it = _clss.begin(); it!=_clss.end(); ++it) {
            if(it->deg()>1) {
                if( it->update_short(_Lsys) && it->deg()==1) {
                    _Lsys.add_lineral( it->get_unit() );
                    _clss.erase(it);
                    goto restart; //restart everytime a new lineral is added!
                }
            }
        }
    } else if(opt.ip==initial_prop_opt::full) {
        //fully reduce all cls with deg>1, and replace all linear ones with _Lsys's linerals
        for(auto it = _clss.begin(); it!=_clss.end(); ++it) {
            if(it->deg()>1) it->update(_Lsys);
            else it = std::prev( _clss.erase(it) );
        }
    }

    //add linerals from _Lsys to lineral_queue
    for(auto& [lt,l_it] : _Lsys.get_pivot_poly_idx()) {
        //_clss.emplace_back( std::move(*l_it) );
        if(!opt.lgj) {
            VERB(90, "c adding new lineral: " << BOLD(l_it->to_str()) << "  --> gives with current assignments: "<<l_it->reduced(alpha).to_str());
            add_new_lineral( *l_it, 0, queue_t::NEW_UNIT, origin_t::INIT );
        } else {
            //IF lgj is enabled, no need to watch the linerals in dl 0
            lineral_watches[0].emplace_back(*l_it, alpha, alpha_dl, dl_count, 0);
            if(opt.pp!=xornado_preproc::no) IG_linerals_to_be_propagated.emplace_back( *l_it );
            //since lgj implementation is sadly NOT complete, so it seems beneficial to do it nonetheless!
            //VERB(90, "c adding new lineral: " << BOLD(l_it->to_str()) << "  --> gives with current assignments: "<<l_it->reduced(alpha).to_str());
            //add_new_lineral( *l_it, 0, queue_t::NEW_UNIT, origin_t::INIT );
        }
    }

    if(opt.lgj) {
        //init lazy_gauss_jordan
        lazy_gauss_jordan = new lin_sys_lazy_GE( std::move(_Lsys), get_num_vars() );
        VERB(120, "c lazy_gauss_jordan: " << lazy_gauss_jordan->to_str() );
        list<lineral>& q = lazy_gauss_jordan->get_implied_literal_queue();
        for (auto&& lin : q) {
            add_new_lineral( std::move(lin), 0, queue_t::NEW_UNIT, origin_t::INIT );
        }
        lazy_gauss_jordan->clear_implied_literal_queue();
    }

    //init utility and tier
    utility = vec<double>(0);
    utility.reserve(xnf_clss.size());
    tier = vec<var_t>(0);
    tier.reserve(xnf_clss.size());
    tier_count[0] = 0;
    tier_count[1] = 0;
    tier_count[2] = 0;
    active_cls = 0; //value is managed by 'init_and_add_xcls_watch'
    //add (possibly) reduced clauses
    for(auto& cls : _clss) {
        if(!cls.is_zero()) init_and_add_cls_watch( std::move(cls), false );
    }

    assert(active_cls+lazy_gauss_jordan->size() >= xnf_clss.size()-std::min(xnf_clss.size(),lineral_queue.size()));

    // init active_cls_stack
    active_cls_stack = vec<var_t>();
    active_cls_stack.emplace_back(active_cls);

    assert(assert_data_structs());
};

void solver::backtrack(const var_t& lvl) {
    if(lvl == dl) return;
    assert(lvl < dl);
    VERB(50, "c " << CYAN("backtracking to dl " << lvl));
    if (dl - lvl > 1) {
        VERB(80, "c " << std::to_string(dl) << " : BACKJUMPING BY MORE THAN ON LEVEL!");
    }
    
    // trail and assignments!
  #ifndef NDEBUG
    if(opt.verb>150) print_trail();
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

    //backtrack GJE
    if(opt.lgj) lazy_gauss_jordan->backtrack(lvl);

    //cleanup lineral_queue
    lineral_queue.clear(lvl);

    // check active_cls count
    //VERB(90, "active_cls restored:   " << std::to_string(active_cls))
    //VERB(90, "active_cls recomputed: " << std::to_string(std::count_if(xnf_clss.begin(), xnf_clss.end(), [&](const cls_watch &cls_w) { return cls_w.is_active(dl_count) && cls_w.is_irredundant(); })))
    assert(active_cls == (var_t) std::count_if(xnf_clss.begin(), xnf_clss.end(), [&](const cls_watch &cls_w) { return cls_w.is_active(dl_count) && cls_w.is_irredundant(); }));

  #ifndef NDEBUG
    if(opt.verb>150) print_trail();
  #endif

    VERB(201, to_str());
    VERB(150, "c backtracking finished!");
    assert(assert_data_structs());
};

// decision heuristics
lineral solver::dh_vsids() {
    assert(!order_heap_vsids.empty());
    var_t ind = 0;
    while (ind==0 || (alpha[ind] != bool3::None && !order_heap_vsids.empty() )) {
        ind = order_heap_vsids.removeMin();
    }
    return lineral( ind, last_phase[ind]==bool3::True);
};

lineral solver::dh_shortest_wl() {
    //find unassigned variable that has the longest watch_list
    var_t lt_min = 0;
    size_t size_min = xnf_clss.size() + 1;
    for(size_t idx=1; idx<watch_list.size(); ++idx) {
        if(alpha[idx]==bool3::None && (watch_list[idx].size() < size_min)) {
            lt_min = idx; size_min = watch_list[idx].size();
        }
    }
    assert(lt_min!=0 && lt_min < (var_t)alpha.size());
    return lineral( lt_min, last_phase[lt_min]==bool3::True);
}

lineral solver::dh_longest_wl() {
    //find unassigned variable that has the longest watch_list
    var_t lt_max = 0;
    size_t size_max = 0;
    for(size_t idx=1; idx<watch_list.size(); ++idx) {
        if(alpha[idx]==bool3::None && (watch_list[idx].size() > size_max)) {
            lt_max = idx; size_max = watch_list[idx].size();
        }
    }
    assert(lt_max!=0 && lt_max < (var_t)alpha.size());

    return lineral( lt_max, last_phase[lt_max]==bool3::True);
}

lineral solver::dh_lex_LT() {
    var_t i = 1;
    while(alpha[i] != bool3::None) ++i;
    assert(i<alpha.size());
    return lineral( i, last_phase[i]==bool3::True);
};

template<const solver::dec_heu_t dh>
lineral solver::dh_gp() {
    var_t idx = 0;
    while (idx < opt.P.size() && alpha[opt.P[idx]] != bool3::None) ++idx;
    if(idx == opt.P.size()) return (this->*dh)();
    const var_t i = opt.P[idx];
    assert(i>0 && alpha[i]==bool3::None);
    return lineral(i, last_phase[i] == bool3::True);
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

void solver::bump_score(const lineral &lit) {
    assert(lit.LT() < activity_score.size());
    //for(const auto l : lit) bump_score(l);
    bump_score(lit.LT()); //@todo bump scores of ALL occuring vars?
};

void solver::decay_score() {
    //instead of actually decaying all scores; we increase the bump
    //@todo slowly decay 'decay' to 0.81 or similar?
    bump *= (1.0 / decay);
};

#ifndef NDEBUG
lineral unit;
#endif

std::pair<var_t, cls_watch> solver::analyze_exp() {
    return analyze();
};

std::pair<var_t, cls_watch> solver::analyze() {
    if(dl<=1) {
        //reason clause is obvious -- negation of first decision!
        return analyze_dpll();
    }

    VERB(70, "**** analyzing conflict");
#ifndef NDEBUG
    print_trail("    *");
#endif
    assert( trails.back().back().ind == 0 ); //ensure last trail entry is a conflict & it comes from an actual clause

#ifdef DEBUG_SLOW
    //ensure trail is supported by reasons
    for(const auto& t_dl : trails) {
        for(const auto& t_el : t_dl) {
            if(t_el.type==trail_t::GUESS) continue;
            const auto rs = get_reason(t_el.lin);
            assert(rs.is_unit(dl_count) && (rs.get_unit().reduced(alpha,equiv_lits)+t_el.lin->to_lineral().reduced(alpha,equiv_lits)).reduced(alpha,equiv_lits).is_zero());
        }
    }
#endif

    cls_watch rs = get_reason(TRAIL.back());
    assert(rs.is_unit(dl_count));
    //fix the ws[0] watch - so far it need not watch the variable with highest alpha_trail_pos
    rs.fix_ws0(alpha, alpha_dl, alpha_trail_pos);
    assert(rs.assert_data_struct(alpha, alpha_trail_pos, dl_count));

    //early abort if clause is already conflict!
    if(rs.size()==1 && rs.linerals[0].is_one()) return {0, std::move(rs)};

    //go through trail of current dl -- skip over irrelevant parts
    cls_watch_resolver learnt_cls(std::move(rs));
    assert(learnt_cls.assert_data_struct(alpha, alpha_trail_pos, dl_count) && learnt_cls.is_unit(dl_count));

    VERB(70, "   * reason clause is   " << BOLD( learnt_cls.to_str() ) << " for UNIT " << learnt_cls.get_unit().to_str() );
    bump_score( TRAIL.back().ind );
    pop_trail(); //remove conflict from trail, i.e., now alpha[0]==bool3:None

    auto it = trails.back().rbegin();
    cls_watch reason_cls;

    //as long as assigning_lvl is dl OR -1 (i.e. equiv-lits are used!), resolve with reason clauses
    while( learnt_cls.get_assigning_lvl(alpha_dl) == dl || learnt_cls.get_assigning_lvl(alpha_dl) == (var_t) -1 ) {
        //assert(false); //add 'is_asserting' to cls_watch_resolver -- shouldn't be too hard to check, right?!
        VERB(70, "   * conflict clause is " << BOLD( learnt_cls.to_str() ) << "   --> gives with current assignments: " << learnt_cls.to_cls().reduced(alpha).to_str());
      #ifndef NDEBUG
        //ensure that clause is conflict clause under alpha
        assert(learnt_cls.is_unit(dl_count) && learnt_cls.get_unit().reduced(alpha).is_one() && !learnt_cls.to_cls().is_zero());
      #endif

        //pop trail until we are at the implied alpha that is watched by learnt_cls (by wl1)
        while( (it->type != trail_t::ALPHA) || (learnt_cls.get_wl0() != it->ind) ) {
            assert(!learnt_cls.unit_contains(it->ind));
            ++it;
            assert(it!=trails.back().rend());
        }
        assert(it->type == trail_t::ALPHA);
        
        //get reason_cls
        reason_cls = get_reason(*it);
        VERB(70, "   * reason clause is   " << BOLD( reason_cls.to_str() ) << " for UNIT " << reason_cls.get_unit().to_str() );

        //ensure that reason cls is reason under alpha
        assert(reason_cls.is_unit(dl_count) && (reason_cls.get_unit().reduced(alpha)+it->lin->to_lineral().reduced(alpha)).reduced(alpha).is_zero());

        learnt_cls.resolve( std::move(reason_cls), alpha, alpha_dl, alpha_trail_pos, dl_count);
    
        //ensure that cls is conflict clause for provided alpha
        assert(learnt_cls.is_unit(dl_count) && learnt_cls.get_unit().reduced(alpha).is_one());

        bump_score( it->ind );
        ++it;
    }
    
    VERB(70, "   * ");
    VERB(70, "   * learnt clause is " << learnt_cls.to_str());

    if(opt.cm) {
        VERB(70, "   * minimize " << learnt_cls.to_str() );
        //minimization
        minimize(learnt_cls);
        VERB(70, "   '------> " << learnt_cls.to_str() );
    }

    VERB(70, "   * finalize " << learnt_cls.to_str() );
    const auto out = learnt_cls.finalize(alpha_dl, alpha_trail_pos, dl_count);
    VERB(70, "   '--------> " << out.to_str() );
    
    VERB(90, "   * XNF " << out.to_xnf_str() );
    VERB(70, "   '----> gives with current assignments: " << out.to_cls().reduced(alpha).to_str());
    assert( out.to_cls().reduced(alpha).to_str() == "1" );
    
    //find correct backtrack-lvl
    const var_t b_lvl = out.get_assigning_lvl(alpha_dl);
    assert(b_lvl < dl);
    //assert that b_lvl is minimal
    assert_slow(b_lvl==0 || !out.to_cls().reduced(alpha,alpha_dl,b_lvl-1).is_unit() || !out.to_cls().reduced(alpha,alpha_dl,b_lvl-1).get_unit().is_assigning());
    
    if( dl < out.size() && b_lvl == dl-1 ) {
        VERB(50, "   * negated decisions lead to smaller learnt_cls and the same backtrack-level!");
    }
    
    VERB(70, "****");
    return std::pair<var_t, cls_watch>(b_lvl, out);
};

std::pair<var_t, cls_watch> solver::analyze_dpll() {
    VERB(70, "**** analyzing dpll-style");
#ifndef NDEBUG
    print_trail("    *");
#endif
    //return negation of last decision!
    assert(!TRAIL.empty());
    //if trail is empty, we are at dl 0, i.e., analyze_dpll should not be called!
    list<lineral> linerals;
    for(auto tr = trails.begin()+1; tr!=trails.end(); ++tr) {
        if(!tr->empty()) linerals.emplace_back( tr->front().ind, !b3_to_bool(alpha[tr->front().ind]) );
    }
    cls_watch learnt_cls( std::move(cls(std::move(linerals))) );
    VERB(70, "   * learnt clause is " << learnt_cls.to_str());
    learnt_cls.init_dpll(alpha, alpha_dl, alpha_trail_pos, dl_count);

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

bool solver::need_restart(stats& s) const {
    if(opt.rst==restart_opt::lbd) {
        if(confl_this_restart > confl_until_restart && forcing_fast > 1.15 * forcing_slow) {
            //restart -- unless blocked!
            if(assigned_var_count <= 1.4 * blocking) {
                return true;
            } else {
                ++s.no_blocked_restarts;
            }
        }
        return false;
    } else {
        return confl_this_restart > confl_until_restart;
    }
};

void solver::update_restart_schedule(const unsigned int &no_restarts) {
    //update confl_until_restart
    switch(opt.rst) {
        case restart_opt::no:
            confl_until_restart = (unsigned int) -1;
            break;
        case restart_opt::fixed:
            confl_until_restart = confl_until_restart_default;
            break;
        case restart_opt::luby:
            confl_until_restart = luby(2, no_restarts) * confl_until_restart_default;
            break;
        case restart_opt::lbd:
            confl_until_restart = 100; //at least 50 conflicts before next restart!
            break;
    }
};

void solver::clause_cleaning(stats& s) {
    ++s.no_deletions;

    //go to dl 0
    const unsigned int no_cls = xnf_clss.size();

    //tier 0 clauses: keep all of them!
    //tier 1 clauses: move less used quarter to tier 3
    //tier 2 clauses: remove less used half
    VERB(80, "c " << CYAN("clause-cleaning: tier0 " << std::to_string(tier_count[0]) << " tier1 " << std::to_string(tier_count[1]) << " tier2 " << std::to_string(tier_count[2]) ) );

    //compute average utilities in each tier:
    double avg_util_tier[3];
    for(var_t i=0; i<xnf_clss.size(); ++i) {
        avg_util_tier[tier[i]] += utility[i];
    }
    avg_util_tier[0] /= tier_count[0];
    avg_util_tier[1] /= tier_count[1];
    avg_util_tier[2] /= tier_count[2];
    VERB(80, "c " << CYAN("avg util: tier0 " << std::to_string(avg_util_tier[0]) << " tier1 " << std::to_string(avg_util_tier[1]) << " tier2 " << std::to_string(avg_util_tier[2]) ) );

    //create copy for later removal!
    vec<cls_watch> cpy; cpy.reserve(xnf_clss.size());
    vec<var_t> tier_cpy; tier_cpy.reserve(xnf_clss.size());

    if(true) {
        double util_cutoff_move   = 0.125 * avg_util_tier[1];
        double util_cutoff_delete = 0.750 * avg_util_tier[2];

        //mark tier 2 clauses for deletion && move tier 1 clauses to tier 2
        for(var_t i=0; i<xnf_clss.size(); ++i) {
            //if(xnf_clss[i].is_sat(dl_count) || (!xnf_clss[i].is_irredundant() && utility[i] < util_cutoff && !xnf_clss[i].is_unit(dl_count) && xnf_clss[i].get_unit_at_lvl()>0) ) {
            if(xnf_clss[i].is_zero() || xnf_clss[i].is_sat0() ) {
                xnf_clss[i].mark_for_removal(); //remove all clauses which are zero or satisfied in dl0!
                --tier_count[tier[i]];
            } else if(tier[i]==1) {
                if(utility[i] < util_cutoff_move && !xnf_clss[i].is_unit(dl_count) && xnf_clss[i].get_unit_at_lvl()>0) {
                    tier[i] = 2;
                    --tier_count[1];
                    ++tier_count[2];
                }
            } else if(tier[i]==2) {
                if(utility[i] < util_cutoff_delete && !xnf_clss[i].is_unit(dl_count) && xnf_clss[i].get_unit_at_lvl()>0) {
                    xnf_clss[i].mark_for_removal();
                    --tier_count[2];
                    assert( xnf_clss[i].is_sat(dl_count) || xnf_clss[i].to_cls().deg()!=1 );
                }
            }
        }
    } else {
        //update util_cutoff -- TODO should we use quantiles?
        double avg_util_redundant = 0;
        for(var_t i=0; i<xnf_clss.size(); ++i) {
            if(!xnf_clss[i].is_irredundant()) avg_util_redundant += utility[i];
        }
        avg_util_redundant /= active_cls;
        util_cutoff = decay*avg_util_redundant;
        //rm 'useless' cls:
        VERB(50, "c clean clause database")
        //mark clauses to be deleted
        for(var_t i=0; i<xnf_clss.size(); ++i) {
            if(xnf_clss[i].is_sat(dl_count) || (!xnf_clss[i].is_irredundant() && utility[i] < util_cutoff && !xnf_clss[i].is_unit(dl_count) && xnf_clss[i].get_unit_at_lvl()>0) ) {
                xnf_clss[i].mark_for_removal();
                assert( xnf_clss[i].is_sat(dl_count) || xnf_clss[i].to_cls().deg()!=1 );
                //adapt tier_count
                --tier_count[tier[i]];
            }
        }
    }

    VERB(50, "c rm clauses")
    assert_slow( assert_data_structs() );
  #ifndef NDEBUG
    //check if reason cls for lineral_watches can be computed correctly
    for(lin_w_it it=lineral_watches[0].begin(); it!=lineral_watches[0].end(); ++it) {
        const auto rs = get_reason( it );
        assert( (rs.is_unit(dl_count) && (rs.get_unit().reduced(alpha,equiv_lits) + it->to_lineral().reduced(alpha,equiv_lits)).reduced(alpha,equiv_lits).is_zero()) );
        //BEWARE this assertion may fail for some 'restart' calls of solver_cpy(!)
    }
  #endif

    //remove all xnf_clss marked for removal + prepare lookup-table for new idxs of reason_clss
    vec<var_t> new_idx; new_idx.reserve(xnf_clss.size());
    vec<double> util_cpy; util_cpy.reserve(xnf_clss.size());
    for(var_t i=0; i<xnf_clss.size(); ++i) {
        if(!xnf_clss[i].is_marked_for_removal()) {
            cpy.emplace_back(std::move(xnf_clss[i]));
            util_cpy.emplace_back( utility[i] );
            tier_cpy.emplace_back( tier[i] );
            new_idx.emplace_back( cpy.size()-1 );
        } else {
            new_idx.emplace_back( (var_t)-1 );
        }
    }
    xnf_clss = std::move(cpy);
    //fix reason_cls idxs for all lineral_watch in lineral_watches[0]
    for(lin_w_it it=lineral_watches[0].begin(); it!=lineral_watches[0].end(); ++it) {
        it->shift_reason_idxs( new_idx );
      #ifdef DEBUG_SLOWER
        const auto rs = get_reason( it );
        assert( (rs.is_unit(dl_count) && (rs.get_unit().reduced(alpha,equiv_lits) + it->to_lineral().reduced(alpha,equiv_lits)).reduced(alpha,equiv_lits).is_zero()) );
        //BEWARE this assertion may fail for some 'restart' calls of solver_cpy(!)
      #endif
    }
    utility = std::move(util_cpy);
    tier = std::move(tier_cpy);
    VERB(80, "c " << CYAN("done:    tier0 " << std::to_string(tier_count[0]) << " tier1 " << std::to_string(tier_count[1]) << " tier2 " << std::to_string(tier_count[2]) ) );
    VERB(50, "c re-init watch_lists")
    //empty watchlists
    for(auto& wl : watch_list) wl.clear();
    //re-fill watchlists!
    for(var_t i=0; i<xnf_clss.size(); ++i) {
        assert( xnf_clss[i].is_irredundant() || !xnf_clss[i].is_sat(dl_count) );
        if(xnf_clss[i].size()>0) watch_list[xnf_clss[i].get_wl0()].emplace_back( i );
        if(xnf_clss[i].size()>1) watch_list[xnf_clss[i].get_wl1()].emplace_back( i );
    }
    assert( assert_data_structs() );
    
    VERB(50, "c removed " << std::to_string( (double) (no_cls-xnf_clss.size()) / no_cls) << "\% clauses.")

    update_cleaning_params();

  #ifdef DEBUG_SLOW
    assert(tier.size() == xnf_clss.size());
    //ensure that tier counts match
    assert( (var_t) std::count_if(tier.begin(), tier.end(), [&](const auto &t) { return t==0; }) == tier_count[0] );
    assert( (var_t) std::count_if(tier.begin(), tier.end(), [&](const auto &t) { return t==1; }) == tier_count[1] );
    assert( (var_t) std::count_if(tier.begin(), tier.end(), [&](const auto &t) { return t==2; }) == tier_count[2] );
  #endif

    assert_slow(assert_data_structs());
}

void solver::restart(stats& s) {
    VERB(50, "c restart")
    ++s.no_restarts;
    confl_this_restart = 0;

    //warm restart: put all inds from trail back into order_heap_vsids and determine how many dl are identical, i.e., with identical decisions!
    //currently only works for dh_vsids!
    var_t backtrack_lvl = dl;
    if(opt.dh == dec_heu::vsids) {
        for(var_t i=1; i<alpha.size(); ++i) {
            if(!order_heap_vsids.inHeap(i)) order_heap_vsids.insert( i );
        }
        //removeMin one-by-one until they do not correspond to the decisions of the corresponding dl!
        var_t lvl = 1;
        while(lvl<dl) {
            auto decision_on_lvl = trails[lvl].front().ind;
            //query next ind from order_heap_vsids which was NOT assigned on previous dl
            var_t ind = 0;
            while(ind==0 || (alpha_dl[ind] < lvl && !order_heap_vsids.empty() )) {
                ind = order_heap_vsids.removeMin();
            }
            if(ind!=decision_on_lvl) {
                //heuristic would choose a different decision on this lvl! i.e. we can only backtrack to lvl-1 (!)
                backtrack_lvl = lvl-1;
                order_heap_vsids.insert( ind );
                break;
            }
            ++lvl;
        }
    }

    backtrack(backtrack_lvl);
    
    if(need_cleaning(s)) {
        clause_cleaning(s);
    }

    update_restart_schedule(s.no_restarts);
    VERB(90, "c restart finished")
  #ifndef NDEBUG
    print_trail("    *");
  #endif
};


bool solver::remove_fixed_alpha() {
    for(const auto& v : vars_to_be_removed) {
        assert(alpha[v]!=bool3::None);
        assert(alpha_dl[v]==0);
        remove_fixed_alpha(v);
    }
    VERB(90, "c " << GREEN("remove_fixed_alpha: removed " << std::to_string(vars_to_be_removed.size()) << " variables") );
    vars_to_be_removed.clear();
    return false;
}

void solver::remove_fixed_alpha(const var_t upd_lt) {
    assert(dl==0);
    assert_slow( assert_data_structs() );
    assert( alpha[upd_lt]!=bool3::None && alpha_dl[upd_lt]==0 );
    const bool3 val = alpha[upd_lt];
    //rm upd_lt from lineral_watches[0] (all other levels are empty!)
    for(lin_w_it lin = lineral_watches[0].begin(); lin!=lineral_watches[0].end(); ++lin) {
        if(lin->is_active(alpha) && !lin->is_equiv() && !lin->watches(upd_lt)) {
            lin->rm(upd_lt, val);
        }
    }
    //rm upd_lt from xnf_clss
    for(auto& cls_w : xnf_clss) {
        if(cls_w.is_active(dl_count)) {
            assert(!cls_w.watches(upd_lt));
            if( cls_w.rm(upd_lt, val, alpha_trail_pos) ) decr_active_cls(&cls_w - &xnf_clss[0]);
            assert( cls_w.assert_data_struct(alpha, alpha_trail_pos, dl_count) );
        }
    }
    VERB(90, "c " << GREEN("remove_fixed_alpha: x" << std::to_string(upd_lt) << " was removed") );

    //BUGGY! -> we might reduce the 'reason' linerals of assignments and loose the corresponding lineral altogether! -> how to determine which linerals to reduce?!?
    ////reduce fixed_alpha also in LGJ
    //if(opt.lgj) {
    //  #ifdef DEBUG_SLOW
    //    lin_sys sys_prev( lazy_gauss_jordan->get_linerals_const() );
    //  #endif
    //    for(auto& lin : lazy_gauss_jordan->get_linerals()) {
    //        if(!lin.is_assigning()) {
    //            lin.rm(upd_lt, val);
    //        }
    //    }
    //  #ifdef DEBUG_SLOW
    //    lin_sys sys_after( lazy_gauss_jordan->get_linerals_const() );
    //    assert( sys_prev == sys_after );
    //  #endif
    //}

    assert_slow( assert_data_structs() );
}

bool solver::remove_fixed_equiv() {
    assert(dl==0);
    assert_slower( assert_data_structs() );

    VERB(120, "c " << GREEN("remove_fixed_equiv start") );
  #ifdef DEBUG_SLOW
    const auto L = get_lineral_watches_lin_sys();
  #endif
    assert(dl==0);

    var_t count = 0;
    //clear L_watch_list
    for(auto& l : L_watch_list) l.clear();
    //rm upd_lt from lineral_watches[0] (all other levels are empty!)
    for(lin_w_it lin = lineral_watches[0].begin(); lin!=lineral_watches[0].end(); ++lin) {
        if(lin->is_active(alpha) && !lin->is_equiv()) {
            //reduce without tracking reason clause -- not neccessary on dl 0
            lin->reduce_no_tracking(alpha, alpha_dl, dl_count, equiv_lits);
            //if lin becomes assigning, push unto lineral_queue
            if(lin->is_assigning(alpha) || (opt.eq && lin->is_equiv())) {
                queue_implied_lineral(lin, 0, origin_t::LINERAL);
                ++count;
                continue;
            }
        }
        //update L_watch_list -- if lin was not added to queue
        if(lin->size()>0) L_watch_list[ lin->get_wl0() ].emplace_back( 0, dl_count[0], lin );
        if(lin->size()>1) L_watch_list[ lin->get_wl1() ].emplace_back( 0, dl_count[0], lin );
    }
    //empty watchlists
    for(auto& wl : watch_list) wl.clear();

    //reduce all xnf_clss
    for(var_t i=0; i<xnf_clss.size(); ++i) {
        if(xnf_clss[i].is_active(dl_count)) {
            const auto reduce_ret = xnf_clss[i].reduce_equiv(alpha, equiv_lits, dl_count);
            //ensure all reductions are made
          #ifdef DEBUG_SLOW
            for(auto& l : xnf_clss[i].get_linerals()) {
                for(auto& v : l.get_idxs()) assert( xnf_clss[i].is_sat(dl_count) || (alpha[v]==bool3::None && !equiv_lits[v].is_active()) );
            }
          #endif
            //propagate as in GCP -- if clause became UNIT or SAT
            switch (reduce_ret) {
            case cls_upd_ret::SAT:
                assert(xnf_clss[i].is_sat(dl_count));
                assert(xnf_clss[i].is_inactive(dl_count));
                // IGNORE THIS CLAUSE FROM NOW ON
                decr_active_cls(i);
                break;
            case cls_upd_ret::UNIT: //includes UNSAT case (i.e. get_unit() reduces with assignments to 1 !)
                ++count;
                assert(xnf_clss[i].is_unit(dl_count));
                assert(xnf_clss[i].is_inactive(dl_count));
                assert(xnf_clss[i].get_unit_at_lvl() == 0);
                //update utility
                ++utility[i];
                // IGNORE THIS CLAUSE FROM NOW ON
                decr_active_cls(i);
                // new lineral
                add_new_lineral( std::move(xnf_clss[i].get_unit()), 0, queue_t::NEW_UNIT, origin_t::CLAUSE );
                if(xnf_clss[i].size()>0) watch_list[xnf_clss[i].get_wl0()].emplace_back( i );
                assert(xnf_clss[i].size()<=1);
                break;
            case cls_upd_ret::NONE:
                assert(xnf_clss[i].is_none(dl_count));
                assert(xnf_clss[i].is_active(dl_count));
                //fill watch-list
                if(xnf_clss[i].size()>0) watch_list[xnf_clss[i].get_wl0()].emplace_back( i );
                if(xnf_clss[i].size()>1) watch_list[xnf_clss[i].get_wl1()].emplace_back( i );
                break;
            }
            assert_slower( xnf_clss[i].assert_data_struct(alpha, alpha_trail_pos, dl_count) );
        }
    }
    VERB(90, "c " << GREEN("remove_fixed_equiv: " << std::to_string(count) << " new linerals") );

    //// BUGGY! too many lins are reduced! -- how to determine quickly which ones to reduce?!
    ////reduce fixed_equiv also in LGJ
    //if(opt.lgj) {
    //  #ifdef DEBUG_SLOWER
    //    lin_sys sys_prev( lazy_gauss_jordan->get_linerals_const() );
    //    for(const auto& eq : equiv_lits) {
    //        if(eq.is_active()) sys_prev.add_lineral( *eq.reason_lin );
    //    }
    //  #endif
    //    for(auto& lin : lazy_gauss_jordan->get_linerals()) {
    //        if(!lin.is_assigning() && !lin.is_equiv()) {
    //            lin.reduce(equiv_lits);
    //        }
    //    }
    //  #ifdef DEBUG_SLOWER
    //    lin_sys sys_after( lazy_gauss_jordan->get_linerals_const() );
    //    assert( sys_prev == sys_after );
    //  #endif
    //}
    
    remove_fixed_equiv_before_next_GCP = false;

    assert_slower( assert_data_structs() );
  #ifdef DEBUG_SLOW
    const auto L_after = get_lineral_watches_lin_sys();
    assert( (L+L_after).to_str() == L_after.to_str() ); //ensure that L <= L_after
  #endif
    return count>0;
}

lineral new_unit;
void solver::GCP(stats &s) noexcept {
    s.no_gcp++;
    VERB(90, "c " << YELLOW("GCP start"));
    start:
    while(!lineral_queue.empty() && !at_conflict()) {
        assert_slow(assert_data_structs());

        const var_t upd_lt = propagate_implied_lineral();
        if(upd_lt == (var_t) -1) continue; //nothing new to propagate!
        if(upd_lt == 0) { assert(at_conflict()); continue; } //at conflict!
        ++s.new_px_upd;
        VERB(120, "c new literal ready for propagation");
        assert( alpha_dl[upd_lt]==dl );

        if(opt.lgj) {
            VERB(120, "c performing lazy gauss jordan elim");
            const auto begin  = std::chrono::high_resolution_clock::now();
            if( lazy_gauss_jordan->assign(upd_lt, alpha, dl) ) {
                //LGJ found new literals
                fetch_LGJ_implications(s);
            }
            const auto end  = std::chrono::high_resolution_clock::now();
            s.total_lgj_time += std::chrono::duration_cast<std::chrono::duration<double>>(end - begin);
        }


        VERB(120, "c updating lineral_watches");
        //(1) find new implied alphas from watched linerals
        var_t i = 0;
        var_t len = L_watch_list[upd_lt].size();
        while(i < len) {
            const auto& [lvl, dl_c, lin] = L_watch_list[upd_lt][i];
            //if *lin might habe been removed and the watching scheme must now be fixed
            if(dl_count[lvl] != dl_c) {
                std::swap(L_watch_list[upd_lt][i], L_watch_list[upd_lt][len-1]);
                --len;
                //it = L_watch_list[upd_lt].erase( it );
                continue;
            }
            assert(lin->watches(upd_lt));
            if(!lin->is_active(dl_count)) {
                ++i;
                continue;
            }
            const auto& [new_wl, ret] = lin->update(upd_lt, alpha, dl, dl_count);
            //if watched-literal has changed, i.e., new_wl != 0; update watch-list
            switch (ret) {
            case lineral_upd_ret::ASSIGNING:
                assert( new_wl == upd_lt );
                assert( lin->is_assigning(alpha) );
                assert( !lin->is_active(alpha) );
                // update alpha
                queue_implied_lineral(lin, dl, origin_t::LINERAL, queue_t::IMPLIED_ALPHA);
                ++i;
                break;
            case lineral_upd_ret::UNIT:
                assert( new_wl != upd_lt );
                assert(!lin->is_assigning(alpha));
                //move to different watch-list
                L_watch_list[new_wl].emplace_back( std::move(L_watch_list[upd_lt][i]) );
                std::swap(L_watch_list[upd_lt][i], L_watch_list[upd_lt][len-1]);
                --len;
                break;
            }
        }
        L_watch_list[upd_lt].resize(len);

        VERB(120, "c updating clauses");
        //(2) find new implied linerals from watched clauses
        var_t i2 = 0;
        var_t len2 = watch_list[upd_lt].size();
        while(i2 < len2) {
            //assert(assert_data_structs());
            const var_t& i = watch_list[upd_lt][i2];
            assert(xnf_clss[i].watches(upd_lt));
            if(!xnf_clss[i].is_active(dl_count)) { ++i2; continue; }
            const auto& [new_wl, ret] = xnf_clss[i].update(upd_lt, alpha, alpha_dl, alpha_trail_pos, dl_count);
            //if watched-literal has changed, i.e., new_wl != 0; update watch-list
            switch (ret) {
            case cls_upd_ret::SAT:
                assert( upd_lt == new_wl );
                assert(xnf_clss[i].is_sat(dl_count));
                assert(xnf_clss[i].is_inactive(dl_count));
                // IGNORE THIS CLAUSE FROM NOW ON
                decr_active_cls(i);
                ++i2;
                break;
            case cls_upd_ret::UNIT: //includes UNSAT case (i.e. get_unit() reduces with assignments to 1 !)
                assert( upd_lt == new_wl );
                assert(xnf_clss[i].is_unit(dl_count));
                assert(xnf_clss[i].is_inactive(dl_count));
                assert(xnf_clss[i].get_unit_at_lvl() == dl);
                //increase utility
                ++utility[i];
                // IGNORE THIS CLAUSE FROM NOW ON
                decr_active_cls(i);
                // new lineral
                // @todo use add_new_lineral
                lineral_watches[dl].emplace_back( std::move(xnf_clss[i].get_unit()), alpha, alpha_dl, dl_count, i, dl);
                queue_implied_lineral( std::prev(lineral_watches[dl].end()), dl, origin_t::CLAUSE );
                ++i2;
                break;
            case cls_upd_ret::NONE:
                assert( upd_lt != new_wl );
                assert(xnf_clss[i].is_none(dl_count));
                assert(xnf_clss[i].is_active(dl_count));
                //move i to watch-list of new_wl
                watch_list[new_wl].emplace_back(i);
                std::swap(watch_list[upd_lt][i2], watch_list[upd_lt][len2-1]);
                --len2;
                break;
            }
        }
        watch_list[upd_lt].resize(len2);
        
        //if we propagated on dl 0, remove all upd_lt from lineral_watches AND from xnf_clss, so that they only occur in the watched clauses.
        assert_slower(assert_data_structs());
        if(dl == 0) remove_fixed_alpha(upd_lt);
    }
    if(need_equiv_removal() && lineral_queue.empty()) {
        if( remove_fixed_equiv() ) goto start;
    }
    assert(lineral_queue.empty() || at_conflict());

    VERB(201, to_str());
    VERB(90, "c " << YELLOW("GCP end"));
    assert_slow(assert_data_structs());
};

// implementation of a dpll-solver
void solver::dpll_solve(stats &s) {
    VERB(25, "c dpll-solving start")
    // return UNSAT if linsys has no solution
    if (at_conflict()) {
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
    
    // stack for lin_sys that store alternative dec
    lin_sys new_lin_sys;
    std::stack<lineral> dec_stack;

    // before anything else: collect implications that were found during initialization in lazy_gauss_jordan.
    if(need_LGJ_update()) find_implications_by_LGJ(s);
    // GCP -- before making decisions!
    goto dpll_gcp;

    while (true) {
        if (s.cancelled.load()) {
            VERB(10, "c cancelled");
            return;
        }
        if (active_cls > 0 || at_conflict()) {
            // make decision / backtrack
            if (at_conflict()) {
                dpll_conflict:
                VERB(25, "c " << std::to_string(dl) << " : " << "conflict --> backtrack!")
                ++s.no_confl;
                // conflict!
                if (dl == 0) {
                    // return UNSAT
                    s.finished = true;
                    s.end = std::chrono::high_resolution_clock::now();
                    
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
                trails.emplace_back( list<trail_elem>() );
                ++s.no_dec;
                // save active_cls count
                assert(active_cls == (var_t) std::count_if(xnf_clss.begin(), xnf_clss.end(), [&](const cls_watch &cls_w) { return cls_w.is_active(dl_count) && cls_w.is_irredundant(); }));
                active_cls_stack.emplace_back(active_cls);
                assert((var_t)active_cls_stack.size() == dl + 1);

                // make new decision!
                // use decisions heuristic to find next decision!
                lineral dec = (this->*decH)();
                VERB(50, "c " << std::to_string(dl) << " : "
                              << "decision " << std::to_string(s.no_dec) << " namely [" << dec.to_str() << "] or [" << dec.plus_one().to_str() << "]")
                //construct alt system
                dec_stack.emplace( dec.plus_one() );
                add_new_guess(std::move(dec));
            }

            dpll_gcp:
            GCP_inprocess(s);
            //in case we did backtrack inside find_implications_by_GE: fix dec_stack!
            while(dec_stack.size()>dl) dec_stack.pop();

            assert((var_t)active_cls_stack.size() == dl + 1);
            assert((var_t)trails.size() == dl + 1);
            assert((var_t)dec_stack.size() == dl);
            assert(assert_data_structs());
        } else {
            //now active_cls == 0 AND !at_conflict(); however the latter only means that alpha[0]!=bool3::True at the moment
            const auto L = get_lineral_watches_lin_sys();
            if (!L.is_consistent()) {
                //enforce backtracking!
                // @todo use add_new_lineral
                lineral_watches[dl].emplace_back( lineral(cnst::one), alpha, alpha_dl, dl_count, dl );
                process_lineral(std::prev(lineral_watches[dl].end()), dl, queue_t::NEW_GUESS, origin_t::GUESS);
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
    if (at_conflict()) {
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
    
    // before anything else: collect implications that were found during initialization in lazy_gauss_jordan.
    if(need_LGJ_update()) find_implications_by_LGJ(s);
    // GCP -- before making decisions!
    GCP_inprocess(s);
    

    while (true) {
        if (s.cancelled.load()) {
            VERB(10, "c cancelled");
            return;
        }
        if (active_cls > 0 || at_conflict()) {
            // make decision / backtrack
            if (at_conflict()) {
                VERB(25, "c " << std::to_string(dl) << " : " << "conflict --> backtrack!")
                ++s.no_confl;
                ++confl_this_restart;
                // conflict!
                if (dl == 0) {
                    // return UNSAT
                    s.finished = true;
                    
                    return;
                }
            
                ///// BACKTRACKING /////
                ///// CLAUSE LEARNING /////
                const auto begin  = std::chrono::high_resolution_clock::now();
                auto [lvl, learnt_cls] = (this->*analyze)();
                const auto end  = std::chrono::high_resolution_clock::now();
                s.total_ca_time += std::chrono::duration_cast<std::chrono::duration<double>>(end - begin);
                

                //@heuristic; when to add this clause?!
                //if( lvl==dl-1 && std::get<0>(learnt_cls.get_unit().get_watch_tuple(alpha_dl, alpha_trail_pos)) != trails.back().front().ind ) {
                //    VERB(50, "c ")
                //    //add dpll-clause as well - if learnt clause is 'too' long?
                //    auto [_, cls] = analyze_dpll();
                //    add_learnt_cls( std::move(cls) );
                //}
                // backtrack
                const auto unit_lvl = learnt_cls.get_unit_at_lvl();
                assert(lvl >= unit_lvl);
                //on unit_lvl a new unit is learnt: if not all decisions are necessary to get the unit assigning, backtrack to unit_lvl.
                if( learnt_cls.get_unit().reduced(alpha, alpha_dl, unit_lvl).LBD(alpha_dl) <= (lvl-unit_lvl) ) {
                    backtrack( unit_lvl );
                } else {
                    backtrack( lvl );
                }

                // update lbd-based restart values
                if(opt.rst==restart_opt::lbd) update_lbd_restart_vals(learnt_cls.LBD(alpha_dl), s);

                // add learnt_cls
                add_learnt_cls( std::move(learnt_cls) );
                // decay score
                decay_score();

                VERB(201, to_str());
                //restart?
                if( need_restart(s) ) {
                    restart(s);
                }
            } else {
                ++dl;
                trails.emplace_back( list<trail_elem>() );
                ++s.no_dec;
                // save active_cls count
                assert(active_cls == (var_t) std::count_if(xnf_clss.begin(), xnf_clss.end(), [&](const cls_watch &cls_w) { return cls_w.is_active(dl_count) && cls_w.is_irredundant(); }));
                active_cls_stack.emplace_back(active_cls);
                assert((var_t)active_cls_stack.size() == dl + 1);

                // make new decision!
                // use decisions heuristic to find next decision!
                lineral dec = (this->*decH)();
                VERB(50, "c " << std::to_string(dl) << " : "
                              << "decision " << std::to_string(s.no_dec) << " namely [" << dec.to_str() << "] or [" << dec.plus_one().to_str() << "]")
                add_new_guess( std::move(dec) );
            }

            cdcl_gcp:
            GCP_inprocess(s);

            assert((var_t)active_cls_stack.size() == dl + 1);
            assert((var_t)trails.size() == dl + 1);
            assert(assert_data_structs());
        } else {
            VERB(25, "c " << std::to_string(dl) << " : " << "no more active clauses --> solution or backtrack!")
            //now active_cls == 0 AND !at_conflict(); however the latter only means that alpha[0]!=bool3::True at the moment
            auto [L,r_cls] = check_lineral_watches_GE();
            if (!L.is_consistent()) {
                backtrack( r_cls.get_assigning_lvl(alpha_dl) );
                add_learnt_cls( std::move(r_cls), false );
                GCP_inprocess(s);
                if(!at_conflict()) ++s.no_confl; //count as conflict here only if we do not need another conflict analysis
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
                    assert( idx>xnf_clss.size() || xnf_clss[idx].is_irredundant() );
                    // decay score
                    decay_score();

                    goto cdcl_gcp;
                }

                return;
            }
        }
    }
};


void solver::solve_L(const lin_sys& L, stats& s) const {
    //compute first sol
    s.sols.emplace_back( vec<bool>(get_num_vars(), false) );
    L.solve( s.sols.back() );
   
    s.finished = true;

    if(s.sols.size()<opt.sol_count) {
        //print sol
        s.print_sol();
        VERB(0, "c solutions found so far: "<<std::to_string(s.sols.size()));
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
        VERB(0, "c solutions found so far: "<<std::to_string(s.sols.size()));
        ++sol_ct;
    }
}


// overwrite to_str() func
std::string solver::to_str() const noexcept {
    // generate string of edges with lexicographic ordering!
    vec<std::string> str(xnf_clss.size());
    // construct strings!
    auto to_str = [&](const cls_watch &cls) -> std::string { return cls.to_str(); };
    std::transform(xnf_clss.begin(), xnf_clss.end(), str.begin(), to_str);
    std::sort(str.begin(), str.end());

    std::stringstream ss;
    std::copy(str.begin(), str.end(), std::ostream_iterator<std::string>(ss, "; "));
    std::string result = ss.str();
    if (!result.empty()) {
        result.resize(result.length() - 1); // trim trailing space
    }

    return result;
}

std::string solver::to_xnf_str() const noexcept {
    auto clss_str = vec<std::string>();
    var_t n_cls = 0;
    //add alpha
    VERB(80, "c printing alpha assignment")
    if (alpha[0] != bool3::None) {
        VERB(85, "instance is UNSAT; print only empty clause.")
        return "p xnf "+std::to_string(get_num_vars())+" 1\n 0\n";
    }
    for(var_t i=1; i<alpha.size(); ++i) {
        if(alpha[i] == bool3::None) continue;
        clss_str.emplace_back( lineral(i, b3_to_bool(alpha[i])).to_xnf_str() + " 0" );
        ++n_cls;
        VERB(85, "c " << clss_str.back());
    }
    VERB(80, "c printing linear polys")
    //add linear polys
    for(const auto& lw_dl : lineral_watches) {
        for(const auto& l : lw_dl) {
            if(!l.is_active(alpha)) continue;
            lineral lin = l.to_lineral();
            lin.reduce(alpha);
            if(lin.is_zero()) continue;
            clss_str.emplace_back( lin.to_xnf_str() + " 0" );
            ++n_cls;
            VERB(85, "c " << clss_str.back());
        }
    }
    VERB(80, "c printing XNF clauses")
    //go through xnf_clss
    for(const auto& cls_w : xnf_clss) {
        if(!cls_w.is_active(dl_count)) continue;
        std::string cls_str = "";
        auto cls = cls_w.to_cls().reduced(alpha);
        for(const auto& lin : cls.get_ass_VS().get_linerals()) {
            cls_str += lin.plus_one().to_xnf_str();
            cls_str += " ";
        }
        clss_str.emplace_back( cls_str + "0" );
        ++n_cls;
        VERB(95, "c " << clss_str.back());
    }
    //convert to one big string
    std::string str = "p xnf "+std::to_string(get_num_vars())+" "+std::to_string(n_cls)+"\n";
    for(const auto &cls : clss_str) {
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

        //check assigned_var_count
        assert( (var_t) std::count_if(alpha.begin(), alpha.end(), [](const auto val){ return val!=bool3::None; }) == assigned_var_count );

        // check data structs of xnf_clss
        for (var_t i = 0; i < xnf_clss.size(); i++) {
            assert(xnf_clss[i].assert_data_struct());
            //only check advanced conditions if lineral_queue is empty!
            if(!at_conflict() && lineral_queue.empty()) assert(xnf_clss[i].assert_data_struct(alpha, alpha_trail_pos, dl_count));
        }

      #ifdef DEBUG_SLOWER
        ////check watch-lists -- if everything is propagated!
        //if(lineral_queue.empty()) {
        //    std::set<var_t> watched_idxs;
        //    auto it = watch_list.begin();
        //    var_t idx = 0;
        //    while(it != watch_list.end()) {
        //        for([[maybe_unused]] auto i : *it) {
        //            assert( xnf_clss[i].watches( idx ) );
        //            if(xnf_clss[i].is_sat0()) continue;
        //            if(xnf_clss[i].is_unit(dl_count) && xnf_clss[i].get_unit_at_lvl()==0) continue;
        //            watched_idxs.insert( i );
        //        }
        //        ++it; ++idx;
        //    }
        //    //calc total number of required watches:
        //    var_t cnt = 0;
        //    for(const auto& cls : xnf_clss) {
        //        if(cls.is_sat0()) continue;
        //        if(cls.is_unit(dl_count) && cls.get_unit_at_lvl()==0) continue;
        //        ++cnt;
        //    }
        //    assert( watched_idxs.size()==cnt );
        //}
        //if(lineral_queue.empty()) {
        //    std::map<std::pair<int,int>, int> watch_cnt;
        //    std::set<lin_w_it> watched_lins;
        //    int idx = 0;
        //    auto it = L_watch_list.begin();
        //    while(it != L_watch_list.end()) {
        //        for([[maybe_unused]] auto [lvl, dl_c, lin] : *it) {
        //            assert( dl_count[lvl]!=dl_c || lin->watches( idx ) || lin->to_lineral().is_constant() );
        //            if(dl_count[lvl]>dl_c) continue;
        //            int idx2 = std::distance(lineral_watches[lvl].begin(), std::find_if(lineral_watches[lvl].begin(), lineral_watches[lvl].end(), [&](auto& l){ return l==*lin; })); //assumes every literal occurs exactly once!
        //            if(watch_cnt.contains({lvl,idx2})) {
        //                watch_cnt[{lvl,idx2}] += 1;
        //            } else {
        //                watch_cnt.insert( {{lvl,idx2}, 1} );
        //            }
        //        }
        //        ++it; ++idx;
        //    }
        //    it = L_watch_list.begin();
        //    int lins_cnt = 0;
        //    int sum_cnt = 0;
        //    while(it != L_watch_list.end()) {
        //        for([[maybe_unused]] auto [lvl, dl_c, lin] : *it) {
        //            if(dl_count[lvl]>dl_c) continue;
        //            //if(lvl==0 && opt.lgj) continue;
        //            //ensure every lineral occurs in two watch-lists!
        //            [[maybe_unused]] int idx2 = std::distance(lineral_watches[lvl].begin(), std::find_if(lineral_watches[lvl].begin(), lineral_watches[lvl].end(), [&](auto& l){ return l==*lin; }));
        //            [[maybe_unused]] var_t ct = watch_cnt.find({lvl,idx2})->second;
        //            assert( lin->is_assigning() || ct%2==0);
        //            if(ct>2) {
        //                //ensure ct = 2* #{lins which are equal and listed inside lineral_watches}
        //                //std::cout << std::count_if(lineral_watches[lvl].begin(), lineral_watches[lvl].end(), [&](auto& l){ return l==*lin; }) << std::endl;
        //                assert( (var_t) (2* std::count_if(lineral_watches[lvl].begin(), lineral_watches[lvl].end(), [&](auto& l){ return l==*lin; }) ) == ct );
        //            }
        //            if(!lin->is_assigning()) { //only count those lins where two watches should be present!
        //                sum_cnt += ct;
        //                ++lins_cnt;
        //            }
        //        }
        //        ++it;
        //    }
        //    assert(2*lins_cnt == sum_cnt); //ensures all lins are watched!

        //    //check that each lineral occurs in corresponding watch-lists!
        //    var_t lvl = 0;
        //    for(const auto& lw_dl : lineral_watches) {
        //        for(const auto& lin : lw_dl) {
        //            if(!at_conflict() && lineral_queue.empty() && !lin.is_assigning()) {
        //                assert( std::any_of(L_watch_list[lin.get_wl0()].begin(), L_watch_list[lin.get_wl0()].end(), [&](auto& p){ return *p.lin==lin; }) );
        //                assert( std::any_of(L_watch_list[lin.get_wl1()].begin(), L_watch_list[lin.get_wl1()].end(), [&](auto& p){ return *p.lin==lin; }) );
        //            }
        //        }
        //        ++lvl;
        //    }
        //}

        //check that all lineral_watches are supported by the units in xnf_clss
        lin_sys L_lin = lin_sys();
        for(const auto& lw_dl : lineral_watches) {
            for(const auto& l : lw_dl) {
                L_lin.add_lineral(l.to_lineral());
            }
        }
        lin_sys L_units = lin_sys();
        for(const auto& cls : xnf_clss) {
            //add units
            if(cls.is_unit(dl_count)) {
                L_units.add_lineral(cls.get_unit());
            }
        }
        //add units on dl 0
        for(const auto& l : lineral_watches[0]) {
            L_units.add_lineral(l.to_lineral());
        }
        //add guesses, i.e., first lineral on each lvl
        for(const auto& lw_dl : lineral_watches) {
            if(!lw_dl.empty()) L_units.add_lineral(lw_dl.front().to_lineral());
        }
        //now L_lin <= L_units
        if(opt.ca!=ca_alg::no) {
            for(const auto& l : L_lin.get_linerals()) {
                assert(L_units.reduce(l).is_zero());
            }
            assert(L_units==L_lin);
        }
      #endif

        //check that only assignments and alpha's backed by trail are assigned
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
        assert_slow( active_cls == (var_t) std::count_if(xnf_clss.begin(), xnf_clss.end(), [&](const cls_watch& cls) { return cls.is_active(dl_count) && cls.is_irredundant(); }) );
        auto dl_count_cpy = dl_count;
        for(var_t lvl = dl; lvl>0; --lvl) {
            ++dl_count_cpy[lvl];
            //VERB(90, "active_cls on lvl " << std::to_string(lvl) << ":   " << std::to_string(active_cls_stack[lvl]));
            //VERB(90, "active_cls recomputed on lvl " << std::to_string(lvl) << ": " << std::to_string(
            //    std::count_if(xnf_clss.begin(), xnf_clss.end(), [&](const cls_watch &cls) { return cls.is_active(dl_count_cpy) && cls.is_irredundant(); })
            //));
            assert_slow( at_conflict() || active_cls_stack[lvl] == (var_t) 
                std::count_if(xnf_clss.begin(), xnf_clss.end(), [&](const cls_watch& cls) { return cls.is_active(dl_count_cpy) && cls.is_irredundant(); })
            );
        }

        //check trail
        for(var_t lvl = 0; lvl<dl; lvl++) {
            for(const auto& [ind, type, origin, rs] : trails[lvl]) {
                assert( alpha[ind]==bool3::None || alpha_dl[ind]<=dl );
            }
        }
        for(const auto& [ind, type, origin, rs] : trails[dl]) {
            assert( alpha[ind]==bool3::None || alpha_dl[ind]<=dl );
        }
        dl_c_t cnt = 1;
        for(var_t lvl=0; lvl<trails.size(); lvl++) {
            cnt += std::count_if(trails[lvl].begin(), trails[lvl].end(), [](const trail_elem& t) { return t.type==trail_t::ALPHA; });
        }
        assert_slow( cnt == stepwise_lit_trail_length );

        //sanity check that reasons of lineral_watches have not been deleted! (& get_lvl() returns correct lvl)
        var_t lvl = 0;
        for(const auto& lin_l : lineral_watches) {
            for(const auto& lin : lin_l) {
                //assert( !lineral_queue.empty() || lin.assert_data_struct(alpha) ); //may fail during GCP...
                assert( std::all_of(lin.get_reason_idxs().begin(), lin.get_reason_idxs().end(), [&](var_t i){ return i < xnf_clss.size(); }) );
                assert( lin.get_lvl()==lvl );
            }
            ++lvl;
        }

        //check that reasons for equiv_lits exist!
        for(var_t i=0; i<equiv_lits.size(); ++i) {
            if(equiv_lits[i].is_active()) {
                assert( equiv_lits[i].reason_lin->is_equiv() );
                assert( equiv_lits[i].reason_lin->get_equiv_lit()==equiv_lits[i].ind );
                assert( equiv_lits[i].reason_lin->LT()==i );
            }
        }

        if(opt.lgj) {
            //check that the linerals in lazy_gauss_jordan are supported by the linerals in lineral_watches[0]
            lin_sys lin0 = lin_sys( list<lineral>(lineral_watches[0].begin(), lineral_watches[0].end()));
            for(const auto& l : lazy_gauss_jordan->get_linerals()) {
                assert( lin0.reduce(l).is_zero() );
            }
            for(const auto& l : lazy_gauss_jordan->get_recovered_linerals()) {
                assert( lin0.reduce(l).is_zero() );
            }
        }

        //check tier_count-consistency with tier!
        assert(tier.size() == xnf_clss.size());
        //ensure that tier counts match
        assert( (var_t) std::count_if(tier.begin(), tier.end(), [&](const auto &t) { return t==0; }) == tier_count[0] );
        assert( (var_t) std::count_if(tier.begin(), tier.end(), [&](const auto &t) { return t==1; }) == tier_count[1] );
        assert( (var_t) std::count_if(tier.begin(), tier.end(), [&](const auto &t) { return t==2; }) == tier_count[2] );
        
        // check solution! (for rand-10-20.xnf) -- may help in debugging!
        /*
        if (opt.num_vars == 10) {
            vec<bool> sol = {false, false, true, false, false, false, false, true, false, true};
            std::cout << "NO SOL for xnf_clss idxs ";
            for (var_t i = 0; i < xnf_clss.size(); ++i) {
                if (!xnf_clss[i].eval(sol)) {
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


#define LEAD YELLOW(lead)
void solver::print_trail(std::string lead) const noexcept {
    const auto to_string = [](var_t i, var_t width) {
        std::stringstream ss;
        ss.width(width);
        ss << std::left << i;
        return ss.str();
    };
  
    if(this->opt.verb < 80) return;
    VERB(80, LEAD);
    VERB(80, LEAD<<" trail");
    VERB(80, LEAD<<" dl pos type");

    var_t w = std::to_string(alpha.size()).length();

    var_t lvl = 0;
    for(const auto& t_dl : trails) {
        var_t i = 0;
        VERB(80, LEAD << YELLOW(" -"));
        for (const auto& t : t_dl) {
            assert( (t.type!=trail_t::ALPHA) || alpha_dl[t.ind] == lvl );
            switch(t.type) {
              case trail_t::EQUIV:
                VERB(80, LEAD<<" " << GRAY(to_string(lvl,w)) << " " << GRAY(to_string(i,w)) << " " << t.type << " " << t.origin << "x" << to_string(t.ind,w) << " -> x" << to_string(equiv_lits[t.ind].ind,w) << (equiv_lits[t.ind].polarity ? "+1" : "  ") << " from " << get_reason(t, 1).to_str());
                break;
              case trail_t::UNIT:
                VERB(80, LEAD<<" " << GRAY(to_string(lvl,w)) << " " << GRAY(to_string(i,w)) << " " << t.type << " " << t.origin <<  t.lin->to_str() << ( lvl>0 ? (" from " + get_reason(t, 1).to_str() ) : "") );
                break;
              case trail_t::ALPHA:
                VERB(80, LEAD<<" " << GRAY(to_string(lvl,w)) << " " << GRAY(to_string(i,w)) << " " << t.type << " " << t.origin << "x" << to_string(t.ind,w) << " -> " << (b3_to_bool(alpha[t.ind]) ? "1" : "0") << "  from " << get_reason(t, 1).to_str());
                break;
              case trail_t::GUESS:
                VERB(80, LEAD<<" " << GRAY(to_string(lvl,w)) << " " << GRAY(to_string(i,w)) << " " << t.type << " " << t.origin << "x" << to_string(t.ind,w) << "    " << " from " << get_reason(t, 1).to_str());
                break;
            }
            ++i;
        }
        ++lvl;
    }
}


bool solver::find_implications_by_GE(stats& s) {
  const auto begin  = std::chrono::high_resolution_clock::now();
  ++s.no_ge;
#ifdef DEBUG_SLOW
  vec<lineral> lits; lits.reserve(lineral_watches.size());
  for(const auto& l_dl : lineral_watches) {
      for(const auto& l : l_dl) lits.emplace_back( l.to_lineral() );
  }
  lin_sys L_( std::move(lits) );
#endif
  VERB(80, "c use M4RI to find implied alpha from linerals");
  list< list<var_t> > r_clss;

  //(1) reduce watched linerals

  //construct matrix only with occuring lits
  vec<var_t> perm(alpha.size(), 0);
  vec<var_t> perm_inv(alpha.size(), 0);
  var_t n_wlins = 0;
  for(const auto& l_dl : lineral_watches) {
    for(const auto& l : l_dl) {
      for(const auto& v : l.get_idxs_()) perm[v] = 1;
      ++n_wlins;
    }
  }
  //apply alpha already? the following does not work, since if x1=0, x2=1 then the literal x1+x2 is omitted, despite resembling a conflict!
  ////ignore all assigned values
  //for(var_t i=0; i<alpha.size(); ++i) {
  //  if(alpha[i]!=bool3::None) perm[i]=0;
  //}
  
  //construct permutation maps
  var_t idx = 0;
  for (var_t i = 1; i < alpha.size(); ++i) { 
    if(perm[i]==1) {
      perm[i] = idx; perm_inv[idx] = i; ++idx;
    }
  }

  const var_t n_vars = idx;
  const rci_t nrows = n_wlins;
  const rci_t ncols = n_vars+1;

  mzd_t* M = mzd_init(nrows, ncols);
  assert( mzd_is_zero(M) );

  //fill with linerals
  rci_t r = 0;
  for(const auto& l_dl : lineral_watches) {
    for(const auto& l : l_dl) {
      //std::cout << l.to_str() << std::endl;
      if(l.has_constant()) {
          mzd_write_bit(M, r, n_vars, 1);
      }
      for(const auto& i : l.get_idxs_()) {
          assert(i>0); assert(perm[i] < (var_t) ncols-1);
          mzd_write_bit(M, r, perm[i], 1);
      }
      ++r;
    }
  }
  assert(r == nrows);
  //store transposed version (required to compute reason clauses)
  mzd_t* M_tr = r>0 ? mzd_transpose(NULL, M) : mzd_init(0,0);
  //TODO not memory efficient! we should really use PLUQ or PLE decomposition below and work from there...
  
  //compute rref
  const rci_t rank = mzd_echelonize_m4ri(M, true, 0); //should we use mzd_echelonize instead?
 
  //read results
  list<lineral> linerals_;
  vec<var_t> idxs;
  for(rci_t r = rank-1; r>0; --r) {
    idxs.clear();
    for(rci_t c=0; (unsigned)c<n_vars; ++c) {
        if( mzd_read_bit(M, r, c) ) {
          idxs.push_back(perm_inv[c]);
          if(idxs.size()>2) continue; //early abort if weight too high
        }
    }
    if(idxs.size()==0) {
      //we got 1, i.e., we have a conflict; all other alpha assignments can be ignored
      assert(linerals_.size()==0);
      assert(mzd_read_bit(M,r,n_vars));
      linerals_.emplace_back( 0, false );
      break;
    } else if(idxs.size()==1 && alpha[idxs[0]]!=to_bool3(mzd_read_bit(M,r,n_vars)) ) {
      linerals_.emplace_back( idxs[0], (bool) mzd_read_bit(M, r, n_vars) );
    } else if(idxs.size()==2 && equiv_lits[idxs[0]].ind==0 && opt.eq) {
      assert(idxs[0] < idxs[1]);
      linerals_.emplace_back( std::move(idxs), (bool) mzd_read_bit(M, r, n_vars), presorted::yes );
    }
  }
  mzd_free(M);
  VERB(80, "c reduction done.");
  // (2) if pure assignment is contained in sys, construct reason cls!
  if(linerals_.size()==0) {
    VERB(80, "c no new alpha-assignments found!")
    mzd_free(M_tr);
    const auto end  = std::chrono::high_resolution_clock::now();
    s.total_linalg_time += std::chrono::duration_cast<std::chrono::duration<double>>(end - begin);
    return false;
  }

  mzd_t* B = mzd_init(std::max(ncols,nrows), linerals_.size());
  VERB(80, "c found "<<std::to_string(linerals_.size())<<" new alpha assignments and equivs");
  idx = 0;
  for(const auto& lit : linerals_) {
    VERB(85, "c   `--> " << lit.to_str());
    //set bits of b according to linerals_
    for(const auto& jdx : lit.get_idxs_()) mzd_write_bit(B, perm[jdx], idx, 1);
    mzd_write_bit(B, n_vars, idx, lit.has_constant()); //uses that supp[0]==0
    ++idx;
  }
  //solve for M^T x = B (i.e. linerals_)
#ifndef NDEBUG
  const auto ret = mzd_solve_left(M_tr, B, 0, true);
  assert(ret == 0);
#else
  mzd_solve_left(M_tr, B, 0, false); //skip check for inconsistency; a solution exists i.e. is found!
#endif
   s.no_ge_prop += linerals_.size();

  //construct corresponding reason clauses
  idx = 0;
  for(auto&& lit : linerals_) {
    VERB(95, "c constructing reason cls indices for "<<lit.to_str());
    
    list<lin_w_it> rs_lins;
    var_t resolving_lvl = 0;
  
  #ifndef NDEBUG
    lineral tmp;
  #endif
  #ifdef DEBUG_SLOWER
    r=0;
    for(var_t lvl=0; lvl<=dl; ++lvl) {
      auto& l_dl = lineral_watches[lvl];
      //check solution:
      for(lin_w_it l_it = l_dl.begin(); l_it != l_dl.end() && r < B->nrows; ++l_it, ++r) {
        if(!mzd_read_bit(B,r,idx)) continue;
        tmp += *l_it;
      }
    }
    assert(L_.reduce(tmp+lit).is_zero());
    tmp.clear();
  #endif
  #ifdef DEBUG_SLOW
    assert( L_.reduce(tmp+lit).is_zero() );
  #endif
    
    r = 0;
    for(var_t lvl=0; lvl<=dl; ++lvl) {
      auto& l_dl = lineral_watches[lvl];
      if(l_dl.empty()) continue;
      for(lin_w_it l_it = l_dl.begin(); l_it != l_dl.end() && r < B->nrows; ++l_it, ++r) {
        if(!mzd_read_bit(B,r,idx)) continue;
      #ifndef NDEBUG
        tmp += *l_it;
      #endif
      #ifdef DEBUG_SLOW
        assert( L_.reduce(tmp+lit).is_zero() );
      #endif
        resolving_lvl = lvl;
        bump_score(*l_it);
        //add all linerals EXCEPT when they come from NEW_GUESS, i.e., are the first lin in l_dl (the 'is_assigning' condition is a workaround to avoid asserts to fail in 'minimize'-calls!)
        if(lvl==0 || l_it!=l_dl.begin() || !l_it->is_assigning()) {
          rs_lins.emplace_back( l_it );
        }
      }
    }
    //post-process r_cls_idxs -- so far r_cls_idxs will lead to a reason clause that ONLY contains GUESS variables; which is potentially cumbersome -- thus: remove all assigning linerals from 'inbetween' decisions-levels
    if(resolving_lvl==0) rs_lins.clear();
    rs_lins.remove_if([&resolving_lvl](const auto& lin){ return lin->get_lvl()!=0 && lin->get_lvl()!=resolving_lvl && lin->is_assigning(); });

    assert((tmp+lit).reduced(alpha).is_zero());
    ++idx;
    //add lineral to lineral_watches
    lineral_watches[resolving_lvl].emplace_back( std::move(lit), alpha, alpha_dl, dl_count, std::move(rs_lins), resolving_lvl );

  #ifndef NDEBUG
    const auto lin = std::prev(lineral_watches[resolving_lvl].end());
    [[maybe_unused]] const auto rcls = get_reason(lin);
    //ensure that reason cls is reason for provided alpha AND equiv_lits
    assert_slow(rcls.is_unit(dl_count) && (rcls.get_unit()+lin->to_lineral()).reduced(alpha,equiv_lits).is_zero());
    //ensure that reason cls is reason for provided alpha
    assert(rcls.is_unit(dl_count) && (rcls.get_unit()+lin->to_lineral()).reduced(alpha).is_zero());
  #endif

    //backtrack if necessary!
    if(resolving_lvl < dl) {
      backtrack(resolving_lvl);
      assert(resolving_lvl==dl);
      queue_implied_lineral(std::prev(lineral_watches[dl].end()), dl, origin_t::LINERAL, queue_t::NEW_UNIT);
      //return immediately
      break;
    }
    assert(resolving_lvl==dl);
    queue_implied_lineral(std::prev(lineral_watches[dl].end()), dl, origin_t::LINERAL, queue_t::NEW_UNIT);
  }

  mzd_free(B);
  mzd_free(M_tr);
  
  const auto end  = std::chrono::high_resolution_clock::now();
  s.total_linalg_time += std::chrono::duration_cast<std::chrono::duration<double>>(end - begin);

  return true;
}

inline lin_sys solver::get_lineral_watches_lin_sys() const {
#ifdef DEBUG_SLOWER
  //simple implementation
  vec<lineral> lits; lits.reserve(lineral_watches.size());
  for(const auto& l_dl : lineral_watches) {
      for(const auto& l : l_dl) lits.emplace_back( l.to_lineral() );
  }
  lin_sys L_( std::move(lits) );
#endif

  //M4RI implementation
  VERB(140, "c use M4RI to reduce watched linerals");

  //(1) reduce watched linerals

  //construct matrix only with occuring lits
  vec<var_t> perm(alpha.size(), 0);
  vec<var_t> perm_inv(alpha.size(), 0);
  var_t n_wlins = 0;
  for(const auto& l_dl : lineral_watches) {
    for(const auto& l : l_dl) {
      for(const auto& v : l.get_idxs_()) perm[v] = 1;
      ++n_wlins;
    }
  }
  //apply alpha already? the following does not work, since if x1=0, x2=1 then the literal x1+x2 is omitted, despite resembling a conflict!
  
  //construct permutation maps
  var_t idx = 0;
  for (var_t i = 1; i < alpha.size(); ++i) { 
    if(perm[i]==1) {
      perm[i] = idx; perm_inv[idx] = i; ++idx;
    }
  }

  const var_t n_vars = idx;
  const rci_t nrows = n_wlins;
  const rci_t ncols = n_vars+1;

  mzd_t* M = mzd_init(nrows, ncols);
  assert( mzd_is_zero(M) );

  //fill with linerals
  rci_t r = 0;
  for(const auto& l_dl : lineral_watches) {
    for(const auto& l : l_dl) {
      //std::cout << l.to_str() << std::endl;
      if(l.has_constant()) {
          mzd_write_bit(M, r, n_vars, 1);
      }
      for(const auto& i : l.get_idxs_()) {
          assert(i>0); assert(perm[i] < (var_t) ncols-1);
          mzd_write_bit(M, r, perm[i], 1);
      }
      ++r;
    }
  }
  assert(r == nrows);
  //store transposed version (required to compute reason clause for )
  mzd_t* M_tr = r>0 ? mzd_transpose(NULL, M) : mzd_init(0,0);
  //TODO not memory efficient! we should really use PLUQ or PLE decomposition below and work from there...
  
  //compute rref
  const rci_t rank = mzd_echelonize_m4ri(M, true, 0); //should we use mzd_echelonize instead?
  
  //mzd_print(M);
  //read results
  list<lineral> linerals_;
  vec<var_t> idxs;
  for(rci_t r = 0; r<rank; ++r) {
    idxs.clear();
    for(rci_t c=0; (unsigned)c<n_vars; ++c) {
        if( mzd_read_bit(M, r, c) ) idxs.push_back(perm_inv[c]);
    }
    linerals_.emplace_back( std::move(idxs), (bool) mzd_read_bit(M, r, n_vars), presorted::yes );
  }

  lin_sys L = lin_sys( std::move(linerals_) );
  assert_slower( L_.to_str() == L.to_str() );
  VERB(140, "c reduction done.");

  mzd_free(M);
  mzd_free(M_tr);
  
  return L;
};


inline std::tuple<lin_sys,cls_watch> solver::check_lineral_watches_GE() {
#ifdef DEBUG_SLOWER
  //simple implementation
  vec<lineral> lits; lits.reserve(lineral_watches.size());
  for(const auto& l_dl : lineral_watches) {
      for(const auto& l : l_dl) lits.emplace_back( l.to_lineral() );
  }
  lin_sys L_( std::move(lits) );
#endif

  //M4RI implementation
  VERB(80, "c use M4RI to reduce watched linerals");

  //(1) reduce watched linerals

  //construct matrix only with occuring lits
  vec<var_t> perm(alpha.size(), 0);
  vec<var_t> perm_inv(alpha.size(), 0);
  var_t n_wlins = 0;
  for(const auto& l_dl : lineral_watches) {
    for(const auto& l : l_dl) {
      for(const auto& v : l.get_idxs_()) perm[v] = 1;
      ++n_wlins;
    }
  }
  //apply alpha already? the following does not work, since if x1=0, x2=1 then the literal x1+x2 is omitted, despite resembling a conflict!
  ////ignore all assigned values
  //for(var_t i=0; i<alpha.size(); ++i) {
  //  if(alpha[i]!=bool3::None) perm[i]=0;
  //}
  
  //construct permutation maps
  var_t idx = 0;
  for (var_t i = 1; i < alpha.size(); ++i) { 
    if(perm[i]==1) {
      perm[i] = idx; perm_inv[idx] = i; ++idx;
    }
  }

  const var_t n_vars = idx;
  const rci_t nrows = n_wlins;
  const rci_t ncols = n_vars+1;

  mzd_t* M = mzd_init(nrows, ncols);
  assert( mzd_is_zero(M) );

  //fill with linerals
  rci_t r = 0;
  for(const auto& l_dl : lineral_watches) {
    for(const auto& l : l_dl) {
      //std::cout << l.to_str() << std::endl;
      if(l.has_constant()) {
          mzd_write_bit(M, r, n_vars, 1);
      }
      for(const auto& i : l.get_idxs_()) {
          assert(i>0); assert(perm[i] < (var_t) ncols-1);
          mzd_write_bit(M, r, perm[i], 1);
      }
      ++r;
    }
  }
  assert(r == nrows);
  //store transposed version (required to compute reason clause for )
  mzd_t* M_tr = r>0 ? mzd_transpose(NULL, M) : mzd_init(0,0);
  //TODO not memory efficient! we should really use PLUQ or PLE decomposition below and work from there...
  
  //for(var_t i=0; i<perm.size(); ++i) {
  //  std::cout << std::to_string(i) << " ";
  //}
  //std::cout << std::endl;
  //for(var_t i=0; i<perm.size(); ++i) {
  //  std::cout << std::to_string(perm[i]) << " ";
  //}
  //std::cout << std::endl;
  //mzd_print(M);

  //compute rref
  const rci_t rank = mzd_echelonize_m4ri(M, true, 0); //should we use mzd_echelonize instead?
  
  //mzd_print(M);
  //read results
  list<lineral> linerals_;
  vec<var_t> idxs;
  for(rci_t r = 0; r<rank; ++r) {
    idxs.clear();
    for(rci_t c=0; (unsigned)c<n_vars; ++c) {
        if( mzd_read_bit(M, r, c) ) idxs.push_back(perm_inv[c]);
    }
    linerals_.emplace_back( std::move(idxs), (bool) mzd_read_bit(M, r, n_vars), presorted::yes );
  }

  lin_sys L = lin_sys( std::move(linerals_) );
  assert_slower( L_.to_str() == L.to_str() );
  VERB(80, "c reduction done.");

  if(L.is_consistent()) {
    mzd_free(M);
    mzd_free(M_tr);
    return {L,cls_watch()};
  }

  // (2) if 1 is contained in sys, construct reason cls!
  assert_slower(!L_.is_consistent());

  VERB(80, "c check_lineral_watches_GE: " << RED("watched linerals are inconsistent!") );

  //solve for M^T x = 1
  mzd_t* b = mzd_init(std::max(ncols,nrows), 1);
  mzd_write_bit(b, n_vars, 0, 1); //uses that supp[0]==0

  //find solution
  //mzd_print(M);
  //std::cout << std::endl;
  //mzd_print(M_tr);
  //std::cout << std::endl;
  //mzd_print(b);
  //std::cout << std::endl;
#ifndef NDEBUG
  const auto ret = mzd_solve_left(M_tr, b, 0, true);
  assert(ret == 0);
#else
  mzd_solve_left(M_tr, b, 0, false); //skip check for inconsistency; a solution exists i.e. is found!
#endif
  //mzd_print(b);
  
  r = 0;
  //resolve cls to get true reason cls
  list<lin_w_it> r_cls_idxs;

#ifndef NDEBUG
  lineral tmp;
#endif
#ifdef DEBUG_SLOWER
  r=0;
  for(var_t lvl=0; lvl<=dl; ++lvl) {
    auto& l_dl = lineral_watches[lvl];
    //check solution:
    for(lin_w_it l_it = l_dl.begin(); l_it != l_dl.end() && r < b->nrows; ++l_it, ++r) {
      if(!mzd_read_bit(b,r,0)) continue;
      tmp += *l_it;
    }
  }
  assert(L_.reduce(tmp).is_zero());
  tmp.clear();
#endif
  
  r = 0;
  var_t resolving_lvl = 0;
  for(var_t lvl=0; lvl<=dl; ++lvl) {
    auto& l_dl = lineral_watches[lvl];
    if(l_dl.empty()) continue;
    for(lin_w_it l_it = l_dl.begin(); l_it != l_dl.end() && r < b->nrows; ++l_it, ++r) {
      if(!mzd_read_bit(b,r,0)) continue;
    #ifndef NDEBUG
      tmp += *l_it;
      assert_slower( L_.reduce(tmp).is_zero() );
    #endif
      resolving_lvl = lvl;
      bump_score(*l_it);
      //add all linerals EXCEPT when they come from NEW_GUESS, i.e., are the first lin in l_dl
      if(lvl==0 || l_it!=l_dl.begin()) {
        r_cls_idxs.emplace_back( l_it );
      }

      #ifdef DEBUG_SLOWER
        const auto rcls = get_reason( l_it );
        //ensure that reason cls is reason for provided alpha
        assert_slow(rcls.is_unit(dl_count) && (rcls.get_unit()+*l_it).reduced(alpha).is_zero());
      #endif
    }
  }
  //post-process r_cls_idxs -- so far r_cls_idxs will lead to a reason clause that ONLY contains GUESS variables; which is potentially cumbersome -- thus: remove all assigning linerals from 'inbetween' decisions-levels
  if(resolving_lvl==0) r_cls_idxs.clear();
  r_cls_idxs.remove_if([resolving_lvl](const auto lin){ return lin->get_lvl()!=0 && lin->get_lvl()!=resolving_lvl && lin->is_assigning(); });

  assert(tmp.reduced(alpha).is_one());
  assert(tmp.is_one());
  
  list<lineral_watch> tmp_l;
  tmp_l.emplace_back( lineral(0,false), alpha, alpha_dl, dl_count, std::move(r_cls_idxs), resolving_lvl );
  const auto lin = tmp_l.begin();

  mzd_free(b);
  mzd_free(M_tr);

#ifdef DEBUG_SLOW
  const auto reason_cls = get_reason( lin );
  //ensure that reason cls is reason for provided alpha
  assert_slow(reason_cls.is_unit(dl_count) && reason_cls.get_unit().reduced(alpha).is_one());
#endif

  return {L, get_reason( lin ) };
}
