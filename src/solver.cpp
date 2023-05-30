#include <iostream>
#include <stack>
#include <deque>
#include <set>
#include <queue>
#include <omp.h>

#include "solver.hpp"

solver::solver(const vec< vec<xlit> >& clss, const options& opt_, const var_t dl_) noexcept : opt(opt_), dl(dl_) {
    #ifndef NDEBUG
        opt.verb = 100;
    #endif

    // init stacks
    state_stack = vec< state_repr >();
    //init watch_list
    watch_list.resize(opt_.num_vars+1);
    L_watch_list.resize(opt_.num_vars+1);
    
    assignments_watch = vec<xlit_watch>(opt_.num_vars + 1, xlit_watch());
    
    // init assignments
    alpha = vec<bool3>(opt_.num_vars + 1, bool3::None);
    alpha_dl = vec<var_t>(opt_.num_vars + 1, 0);
    assignments = vec<xlit>(opt_.num_vars + 1, xlit());
    assignments_dl = vec<var_t>(opt_.num_vars + 1, 0);
    equiv_lits = vec<var_t>(opt_.num_vars+1, 0);
    dl_count = vec<var_t>(opt_.num_vars+1, 1); 
    reason_UNIT = vec<var_t>(opt_.num_vars + 1, -1);
    reason_ALPHA = vec<var_t>(opt_.num_vars + 1, -1);
    trail = std::list<var_t>();
    last_phase = vec<bool3>(opt_.num_vars + 1, bool3::None);

    // vec of pure literals
    vec<xlit> _L = vec<xlit>();

    xclss = vec<xcls_watch>(0);
    xclss.reserve(clss.size());
    

    var_t no_zero_cls = 0;
    // run through xor-clauses to find lineq and construct watch-literals
    for (var_t i = 0; i < clss.size(); i++) {
        xcls cls = xcls(clss[i]); 
        //check if clause reduces to unit
        if (cls.deg() == 1) { // lin-eq!
            _L.emplace_back( cls.get_ass_VS().get_non_zero_el().add_one() );
        } else if (cls.is_zero()) {
            no_zero_cls++;
        } else {
            //add xcls_watch
            init_and_add_xcls_watch( std::move(cls) );
        }
    }
    active_cls = clss.size() - _L.size() - no_zero_cls; // count only non-linear cls!
    assert(active_cls == xclss.size());

    //init gcp_queue
    gcp_queue = std::queue<var_t>();
    assignments_xsys = xsys();
    
    //init upd_queue and add xlits
    upd_queue = std::queue<var_t>();
    for(const auto& lit : _L) add_new_xlit(lit, -1, 0);

    // init activity_score
    activity_score = vec<unsigned int>(opt.num_vars + 1, 1);
    for (var_t i = 0; i < opt.num_vars+1; i++) {
        activity_score[i] += watch_list[i].size();
    }

    // init state_stack
    save_state();

    assert(assert_data_structs());
};

void solver::save_state() {
    //state_stack.emplace_back(active_cls, assignments);
    state_stack.emplace_back(active_cls, assignments_xsys, trail.size());
    assert((var_t)state_stack.size() == dl + 1);
};

void solver::backtrack(const var_t& lvl) {
    VERB(90, "BACKTRACK start");
    assert(assert_data_structs());
    assert(lvl < dl);
    VERB(80, "c backtracking to dl " << lvl);
    ///// --------------- /////
    if (dl - lvl > 1) VERB(80, "c " << std::to_string(dl) << " : BACKJUMPING BY MORE THAN ON LEVEL!");
    // update dl_count
    for(var_t dl_ = dl; dl_>lvl; dl_--) dl_count[dl_]++;
    // adapt dl
    dl = lvl;
    ///// --------------- /////

    // trail and assignments!
    print_trail();
    print_assignments();

    //backtrack state
    while ((var_t)state_stack.size() > dl + 2) state_stack.pop_back();

    // revert assignments and alpha, and reset trail and reasons
    while(trail.size()>state_stack.back().trail_length) { pop_trail(); };
    // revert active_cls count
    active_cls = state_stack.back().active_cls;
    //VERB(90, "active_cls restored:   " + std::to_string(active_cls))
    //VERB(90, "active_cls recomputed: " + std::to_string(std::count_if(xclss.begin(), xclss.end(), [&](const xcls_watch &xcls_w) { return xcls_w.is_active(dl_count); })))
    assert(active_cls == std::count_if(xclss.begin(), xclss.end(), [&](const xcls_watch &xcls_w) { return xcls_w.is_active(dl_count); }));
    //active_cls = std::count_if(xclss.begin(), xclss.end(), [&](const xcls_watch &xcls_w) { return xcls_w.is_active(dl_count); });
    // revert assignments_xsys
    assignments_xsys = std::move(state_stack.back().L);
    state_stack.pop_back();

    //cleanup gcp_queue
    while(!gcp_queue.empty()) gcp_queue.pop();
    while(!upd_queue.empty()) upd_queue.pop();

    print_trail();
    print_assignments();
    // restore/update assignments
    //for(const auto [lt,idx] : assignments_xsys.get_pivot_poly_idx()) {
    //    assert( assignments[lt].is_zero() || assignments_dl[lt] <= lvl );
    //    if(assignments_dl[lt] == 0) {
    //        assignments[lt] = assignments_xsys.get_xlits(idx);
    //        assignments_dl[lt] = lvl;
    //        trail.emplace_back(lt);
    //        reason_UNIT.emplace_back(-2); //TODO what is the reason here?!
    //        alpha[lt] = assignments[lt].as_bool3();
    //        if(alpha[lt]!=bool3::None) {
    //            alpha_dl[lt] = dl;
    //            gcp_queue.emplace(lt);
    //        }
    //    }
    //}
    //find new implied xlits
    //find_implied_alpha();

    VERB(90, to_str());
    VERB(90, "BACKTRACK end");
    assert(assert_data_structs());
};

// decision heuristics
std::pair<xsys, xsys> solver::dh_vsids_UNFINISHED() const {
    return dh_lex_LT();
    var_t i = 0;
    while (!xclss[i].is_active(dl_count))
        i++;
    xlit fc = xclss[i].get_first();
    fc.reduce(assignments);
    return std::pair<xsys, xsys>(xsys(fc.plus_one()), xsys(fc));
    //get inital guess
    //var_t i = 0;
    //while (!xclss[i].is_active()) ++i;
    //xlit guess = xclss[i].get_first();
    ////find optimum!
    //while(i<xclss.size()) {
    //    if(!xclss[i].is_active() ) { ++i; continue; }
    //    for(cls_size_t j = 0; j<xclss[i].size(); ++j) {
    //        if(activity_score[xclss[i].LT(j)] > activity_score[guess.LT()]) {
    //            guess = xclss[i].get_assVS().get_xlits(j);
    //        }
    //    }
    //    ++i;
    //}
    //return std::pair<xsys, xsys>(xsys(guess.plus_one()), xsys(guess));
};

std::pair<xsys, xsys> solver::dh_shortest_wl() const {
    //find unassigned variable that has the longest watch_list
    var_t lt_min = 0;
    size_t size_min = assignments.size();
    for(size_t idx=0; idx<watch_list.size(); ++idx) {
        if(assignments[idx].is_zero() && (watch_list[idx].size() < size_min)) {
            lt_min = idx; size_min = watch_list[idx].size();
        }
    }
    assert(lt_min!=0 && lt_min < (var_t)assignments.size());

    xlit xi = xlit( lt_min, last_phase[lt_min]==bool3::True);
    return std::pair<xsys, xsys>(xsys(xi), xsys(xi.plus_one()));
}

std::pair<xsys, xsys> solver::dh_longest_wl() const {
    //find unassigned variable that has the longest watch_list
    var_t lt_max = 0;
    size_t size_max = 0;
    for(size_t idx=0; idx<watch_list.size(); ++idx) {
        if(assignments[idx].is_zero() && (watch_list[idx].size() > size_max)) {
            lt_max = idx; size_max = watch_list[idx].size();
        }
    }
    assert(lt_max!=0 && lt_max < (var_t)assignments.size());

    xlit xi = xlit( lt_max, last_phase[lt_max]==bool3::True);
    return std::pair<xsys, xsys>(xsys(xi), xsys(xi.plus_one()));
}

std::pair<xsys, xsys> solver::dh_lex_LT() const {
    var_t i = 1;
    while(!assignments[i].is_zero()) ++i;
    assert(i<assignments.size());
    //xlit xi = xlit( std::move( vec<var_t>({i}) ), (last_phase[i]==bool3::True), true );
    xlit xi = xlit( i, last_phase[i]==bool3::True);
    //xlit xi = xlit( (last_phase[i]==bool3::True) ? vec<var_t>({0,i}) : vec<var_t>({i}) );
    //xlit xi = xlit( vec<var_t>({i}) );
    return std::pair<xsys, xsys>(xsys(xi), xsys(xi.plus_one()));
    //return std::pair<xsys, xsys>(xsys(xi.plus_one()), xsys(xi));
};


void solver::bump_score(const xlit &lit) {
    assert(lit.LT() >= 0 && lit.LT() < activity_score.size());
    activity_score[lit.LT()] += bump;
};

void solver::bump_score(const xsys &new_xsys) {
    for (const auto &[lt, _] : new_xsys.get_pivot_poly_idx()) {
        assert(lt >= 0 && lt < activity_score.size());
        activity_score[lt] += bump;
    }
};

void solver::decay_score() {
    for (auto &s : activity_score) {
        s = ceil(s * decay); // TODO make more efficient?! (since result of mult first is float and then is casted back to unsigned int...)
    }
};

xcls solver::get_last_reason() const {
    vec<xlit> lits = vec<xlit>();
    // if reason_UNIT.back() == -1, i.e., trail entry comes from guess, return empty reason-cls
    if (reason_UNIT[trail.back()] >= xclss.size()) {
        lits.push_back( xlit(vec<var_t>({0})) );
        return xcls(lits);
    }
    const xcls_watch &cls = xclss[reason_UNIT[trail.back()]];
    assert(cls.is_unit(dl_count));
    return cls.to_xcls();
};

bool is_subspace(const xsys U, const xsys L) {
    return !L.is_consistent() || (U+L == L);
}

std::pair<var_t, xcls> solver::analyze_exp() {
    VERB(70, "**** analyzing conflict");
#ifndef NDEBUG
    print_assignments("    *");
    print_trail("    *");
#endif
    VERB(70, "   * conflict clause " + get_last_reason().to_str());

    VERB(70, "   * trail in current dl");
    //go through trail of current dl -- skip over irrelevant parts
    xcls learnt_cls = get_last_reason();
    VERB(70, "   * reason clause " + learnt_cls.to_str() + " for UNIT " + assignments[trail.back()].to_str());
    pop_trail();

    vec<xlit> lits;
    vec<xsys> Ls;
    vec<xsys> Ls_dl;
    var_t c_dl = 0;
    Ls.emplace_back( lits );
    for(const auto& t : trail) {
        if(assignments_dl[t]>c_dl) {
            c_dl = assignments_dl[t];
            Ls_dl.push_back(Ls.back());
        }
        lits.push_back( assignments[t] );
        Ls.emplace_back( lits );
        VERB(100, "   * L("+std::to_string(Ls.size()-2)+")   : " + Ls.back().to_str());
    }
    assert(is_subspace(learnt_cls.get_ass_VS(), Ls.back()));
    assert(dl == Ls_dl.size());
    Ls.pop_back();

    while(!trail.empty() && assignments_dl[trail.back()] >= dl && (reason_UNIT.back() < xclss.size())) {
    //while(!trail.empty() && is_subspace(learnt_cls.get_ass_VS(), Ls.back()) && (reason_UNIT.back() < xclss.size())) {
        assert(reason_UNIT.back() > xclss.size() || xclss[reason_UNIT.back()].is_unit(dl_count));
        while(is_subspace(learnt_cls.get_ass_VS(), Ls.back())) {
            // rm from trail (before computing L)
            pop_trail();
            Ls.pop_back();
            VERB(70, "   * backtracking on trail! (c_dl = "+std::to_string(assignments_dl[trail.back()])+")");
        }
        assert(!is_subspace(learnt_cls.get_ass_VS(), Ls.back()));
        if(reason_UNIT.back() > xclss.size()) { pop_trail(); Ls.pop_back(); break; }
        
        const auto tmp_cls = xcls( learnt_cls.update(Ls_dl.back()) );
        VERB(70, "   * conflict clause on prev dl is "+tmp_cls.to_str());
        if( tmp_cls.is_unit() || tmp_cls.is_zero() ) {
            VERB(50, "   * 1UIP! ");
            break; 
        }

        //check conflict cls
        //xsys L = Ls.back();
        VERB(70, "   * conflict clause " + learnt_cls.to_str());
        VERB(70, "   '----> gives with current assignments: " + learnt_cls.update(Ls.back()).to_str());
        assert(learnt_cls.update(Ls.back()).deg() == 1);
        xlit u = learnt_cls.update(Ls.back()).get_ass_VS().get_non_zero_el();
        VERB(70, "   ' unit u:  " + u.to_str());
        //get reason_UNIT clause
        xcls r_cls = get_last_reason();
        VERB(70, "   * reason clause " + r_cls.to_str() + " for UNIT " + assignments[trail.back()].to_str());
        VERB(70, "   '----> gives with current assignments: " + r_cls.update(Ls.back()).to_str());
        assert(u.to_str() == r_cls.update(Ls.back()).to_str());
        pop_trail();
        const xsys L_old = Ls.back();
        Ls.pop_back();

        //check implied unit of r_cls
        auto tmp = xcls( learnt_cls.get_ass_VS() );
        VERB(70, "   ' tmp:  " + tmp.to_str());
        tmp = tmp.update(assignments);
        VERB(70, "   ' tmp:  " + tmp.to_str());
        assert(tmp.is_unit());
        xlit l_cls_implied_unit = tmp.get_unit();
        VERB(70, "   ' implied unit C: " + l_cls_implied_unit.to_str());
        //learnt_cls = xcls( learnt_cls.get_ass_VS()+xsys(u) );
 
        //r_cls = xcls( r_cls.get_ass_VS()+xsys(u.plus_one()) );
        auto tmp2 = xcls( r_cls.get_ass_VS() );
        VERB(70, "   ' tmp2: " + tmp2.to_str());
        tmp2 = tmp2.update(assignments);
        VERB(70, "   ' tmp2: " + tmp2.to_str());
        assert(tmp2.is_unit());
        xlit r_cls_implied_unit = tmp2.get_unit();
        VERB(70, "   ' implied unit R: " + r_cls_implied_unit.to_str());

        //learnt_cls = sres_opt(r_cls, learnt_cls);
        assert(!learnt_cls.is_zero());
        //if(r_cls.is_zero()) continue;
        assert(!r_cls.is_zero());
        //compute sys of assignments in trail
        xsys VC = learnt_cls.get_ass_VS();
        xsys VR = r_cls.get_ass_VS();
        VERB(70, "   * L("+std::to_string(Ls.size()-1)+")   : " + L_old.to_str());
        VERB(70, "   * V_C : " + VC.to_str());
        VERB(70, "   * V_R : " + VR.to_str());
        VERB(70, "   * V_C+V_R : " + (VC+VR).to_str());
        vec<xlit> VC_int_L = intersectVS( VC, L_old );
        vec<xlit> VR_int_L = intersectVS( VR, L_old );
        vec<xlit> VR_int_VC = intersectVS( VR, VC );
        VERB(70, "   * V_C int L : " + xsys(VC_int_L).to_str());
        VERB(70, "   * V_R int L : " + xsys(VR_int_L).to_str());
        VERB(70, "   * V_R int V_C : " + xsys(VR_int_VC).to_str());
        auto VR_plus_VC_int_L = intersectVS( VR+VC, L_old );
        VERB(70, "   * V_R+V_C int L : " + xsys(VR_plus_VC_int_L).to_str());
        assert( (int) VC_int_L.size()+1 == VC.dim());
        assert( (int) VR_int_L.size()+1 == VR.dim());
        if((VC+VR).is_consistent()) {
            xlit ext = (r_cls_implied_unit + l_cls_implied_unit).plus_one();
            VERB(70, "   * extension required!");
            VR += xsys( ext );
            //VR += xsys( l_cls_implied_unit );
            //VC += xsys( r_cls_implied_unit );
            VERB(70, "   * V_C : " + VC.to_str());
            VERB(70, "   * V_R : " + VR.to_str());
            VERB(70, "   * V_C+V_R : " + (VC+VR).to_str());
            VC_int_L  = intersectVS( VC, L_old );
            VR_int_L  = intersectVS( VR, L_old );
            VR_int_VC = intersectVS( VR, VC );
            VERB(70, "   * V_C int L : " + xsys(VC_int_L).to_str());
            VERB(70, "   * V_R int L : " + xsys(VR_int_L).to_str());
            VERB(70, "   * V_R int V_C : " + xsys(VR_int_VC).to_str());
            VR_plus_VC_int_L = intersectVS( VR+VC, L_old );
            VERB(70, "   * V_R+V_C int L : " + xsys(VR_plus_VC_int_L).to_str());
            assert( (int) VC_int_L.size()+1 == VC.dim());
            assert( (int) VR_int_L.size()+1 == VR.dim());
            assert( xsys(VR_int_L) + xsys(l_cls_implied_unit) == VR );
            assert( xsys(VC_int_L) + xsys(l_cls_implied_unit.plus_one()) == VC );
        }
        assert(!(VC+VR).is_consistent());
        //compute new learnt_cls with VS: (V_C int L) + (V_R int L)
        lits.clear();
        std::move(VC_int_L.begin(), VC_int_L.end(), std::back_inserter(lits));
        std::move(VR_int_L.begin(), VR_int_L.end(), std::back_inserter(lits));
        VERB(70, "   * S : " + xsys(lits).to_str());
        learnt_cls = xcls( std::move(xsys(lits)) );
        //VERB(70, "   * sres : " + sres_opt(r_cls, learnt_cls).to_str());

        VERB(70, "   '----> resolution gives clause " + learnt_cls.to_str());
        VERB(70, "   '----> gives with current assignments: " + learnt_cls.update(assignments).to_str());
        
        assert( is_subspace(learnt_cls.get_ass_VS(),L_old) );

        // TODO stop conflict analysis as soon as learnt_cls with assignments up to prev dl reduces to XOR-lit
        // meanwhile only check if it learnt_cls is a pure XOR-lit!
        if (learnt_cls.deg() == 1) break;
    }
    // clean-up trail!
    while (!trail.empty() && assignments_dl[trail.back()] >= dl) {
        pop_trail();
        Ls.pop_back();
    }

//    
//    while(is_subspace(learnt_cls.get_ass_VS(), Ls.back())) {
//        // rm from trail (before computing L)
//        pop_trail();
//        Ls.pop_back();
//        VERB(70, "   * backtracking on trail! (c_dl = "+std::to_string(assignments_dl[trail.back()])+")");
//    }
//    

    VERB(70, "   * ");
    VERB(70, "   * learnt clause is " + learnt_cls.to_str());
    if(!Ls.empty()) {
        assert(!is_subspace(learnt_cls.get_ass_VS(), Ls.back()));
        VERB(70, "   * L("+std::to_string(Ls.size()-1)+")   : " + Ls.back().to_str());
    }
    VERB(70, "   '----> gives with current assignments: " + learnt_cls.update(assignments).to_str());

#ifndef NDEBUG
    print_assignments("    *");
    print_trail("    *");
#endif
    const var_t b_lvl = assignments_dl[trail.back()];
    if( assignments_dl[trail.back()] < learnt_cls.deg() && b_lvl == dl-1 ) {
        VERB(50, "   * negated decisions lead to smaller learnt_cls and the same backtrack-level!");
        //assert(false);
    }
    
    VERB(70, "****");
    return std::pair<var_t, xcls>(b_lvl, learnt_cls);
};

std::pair<var_t, xcls> solver::analyze() {
    VERB(70, "**** analyzing conflict");
#ifndef NDEBUG
    print_assignments("    *");
    print_trail("    *");
#endif
    VERB(70, "   * conflict clause " + get_last_reason().to_str());

    VERB(70, "   * trail in current dl");
    //go through trail of current dl -- skip over irrelevant parts
    std::set<var_t> relevant_lts;
    xcls learnt_cls = get_last_reason();
    VERB(70, "   * reason clause " + learnt_cls.to_str() + " for UNIT " + assignments[trail.back()].to_str());
    //go through conflict clause, identify relevant reducers
    for(const xlit& l : learnt_cls.get_ass_VS().get_xlits()) {
        auto reds = l.reducers(assignments);
        for(const auto& lt : reds)
            relevant_lts.insert(lt);
    }
    // rm from trail
    pop_trail();

    while (!trail.empty() && assignments_dl[trail.back()] >= dl) {
        assert(reason_UNIT.back() > opt.num_vars + 1 || xclss[reason_UNIT.back()].is_unit(dl_count));
        if (relevant_lts.contains(trail.back())) {
            relevant_lts.erase(trail.back());
            // get reason_UNIT clause
            xcls r_cls = get_last_reason();
            // update relevant_lts
            for (const xlit &l : r_cls.get_ass_VS().get_xlits()) {
                auto reds = l.reducers(assignments);
                for (const auto &lt : reds)
                    relevant_lts.insert(lt);
            }
            // const xcls_watch& cls = xclss[reason_UNIT.back()];
            // const cls_size_t u_idx = cls.get_unit_idx();
            // std::move( cls.to_xlit(u_idx)+cls.orig_xlit(u_idx) );
        
            VERB(70, "   * reason clause " + r_cls.to_str() + " for UNIT " + assignments[trail.back()].to_str());
            learnt_cls = sres_opt(r_cls, learnt_cls);
            // rm from trail
            pop_trail();
            VERB(70, "   '----> resolution gives clause " + learnt_cls.to_str());
            VERB(70, "   '----> gives with current assignments: " + learnt_cls.update(assignments).to_str());
        } else {
            // skipping implication, since its irrelevant!
            VERB(70, " SKIPPING * reason clause " + get_last_reason().to_str() + " for UNIT " + assignments[trail.back()].to_str());
            // rm from trail
            pop_trail();
        }

        // TODO stop conflict analysis as soon as learnt_cls with assignments up to prev dl reduces to XOR-lit
        // meanwhile only check if it learnt_cls is a pure XOR-lit!
        if (learnt_cls.deg() == 1) break;
    }
    VERB(70, "   * ");
    VERB(70, "   * learnt clause is " + learnt_cls.to_str());

    // clean-up trail!
    while (!trail.empty() && assignments_dl[trail.back()] >= dl) { pop_trail(); }

    VERB(70, "****");
    assert(false);
    return std::pair<var_t, xcls>(dl - 1, learnt_cls);
};

std::pair<var_t, xcls> solver::analyze_no_sres() {
    VERB(70, "**** analyzing conflict");
#ifndef NDEBUG
    print_assignments("   *");
#endif
    VERB(70, "   * conflict clause " + get_last_reason().to_str());

    VERB(70, "   * trail in current dl");
    // go through trail of current dl -- skip over irrelevant parts
    std::set<var_t> relevant_lts;
    xcls learnt_cls = get_last_reason();
    VERB(70, "   * reason clause " + learnt_cls.to_str() + " for UNIT " + assignments[trail.back()].to_str());
    // go through conflict clause, identify relevant reducers
    for (const xlit &l : learnt_cls.get_ass_VS().get_xlits()) {
        auto reds = l.reducers(assignments);
        for (const auto &lt : reds)
            relevant_lts.insert(lt);
    }
    // rm from trail
    pop_trail();

    while (!trail.empty() && assignments_dl[trail.back()] >= dl && reason_UNIT.back() <= xclss.size()) {
        assert(xclss[reason_UNIT.back()].is_unit(dl_count));
        if (relevant_lts.contains(trail.back())) {
            relevant_lts.erase(trail.back());
            // get reason_UNIT clause
            xcls r_cls = get_last_reason();
            // update relevant_lts
            for (const xlit &l : r_cls.get_ass_VS().get_xlits()) {
                auto reds = l.reducers(assignments);
                for (const auto &lt : reds)
                    relevant_lts.insert(lt);
            }
            VERB(70, "   * reason clause " + r_cls.to_str() + " for UNIT " + assignments[trail.back()].to_str());
        } else {
            // skipping implication, since its irrelevant!
            VERB(70, " SKIPPING * reason clause " + get_last_reason().to_str() + " for UNIT " + assignments[trail.back()].to_str());
        }
        // rm from trail
        pop_trail();
    }
    VERB(70, "   * ");

    // construct learnt clause as in CNF-CDCL by combining assignments corr to relevant_lts
    vec<xlit> lits;
    var_t backtrack_lvl = 0;
    var_t ass_in_cur_dl = 0;
    for (const auto &lt : relevant_lts) {
        if (backtrack_lvl < assignments_dl[lt] && assignments_dl[lt] < dl)
            backtrack_lvl = assignments_dl[lt];
        if (assignments_dl[lt] == dl)
            ++ass_in_cur_dl;
        lits.emplace_back(assignments[lt]);
    }
    learnt_cls = xcls(xsys(lits));
    pop_trail();

    VERB(70, "   * learnt clause is " + learnt_cls.to_str());
    VERB(70, "   '----> gives with current assignments: " + learnt_cls.update(assignments).to_str());
    VERB(70, "   * backjumping to lvl " + std::to_string(backtrack_lvl));

    assert(backtrack_lvl < dl);
    // assert(ass_in_cur_dl==1);

    // clean-up trail!
    while (!trail.empty() && assignments_dl[trail.back()] >= dl) { pop_trail(); }

    VERB(70, "****");
    // assert(false);
    return std::pair<var_t, xcls>(backtrack_lvl, learnt_cls);
};
    
std::pair<var_t,xcls> solver::analyze_dpll() {
    VERB(60, "analyze_dpll called!")
#ifndef NDEBUG
    print_assignments("    *");
    print_trail("    *");
#endif
    //return negation of last decision!
    assert(!trail.empty());
    //if trail is empty, we are at dl 0, i.e., analyze_dpll should not be called!
    xlit dec;
    //go through trail until we are at last decision:
    while(!trail.empty()) {
        //if( (trail.size()==1) || (assignments_dl[trail[ (trail.size()-1) -1 ]] < dl) ) {
        if( (trail.size()==1) || (assignments_dl[*(----trail.end())] < dl) ) {
            dec = assignments[trail.back()];
            pop_trail();
            break;
        }
        pop_trail();
    };
    //now accumulate all previous decisions
    vec<var_t> decision_vars;
    assert(trail.size() == reason_UNIT.size());
    auto t_it = trail.begin();
    auto r_it = reason_UNIT.begin();
    vec<xlit> xlits;
    while(t_it != trail.end()) {
        if(*r_it >= xclss.size()) xlits.push_back(assignments[*t_it].plus_one());
        ++r_it; ++t_it;
    }
    xlits.emplace_back(dec.plus_one());
    xcls learnt_cls(xlits);
    //TODO incorrect!!
    VERB(70, "   * learnt clause is " + learnt_cls.to_str());
    VERB(70, "   '----> gives with current assignments: " + learnt_cls.update(assignments).to_str());

    return {dl-1, learnt_cls};
};

void solver::add_learnt_cls(xcls&& cls) {
    assert(assert_data_structs());
    //assert(cls.deg()>1); //IF THIS FAILS ADD PROPER HANDLING FOR LIN-CLAUSES! (add to xsys directly!)
    if(cls.deg()==1) {
        assert(dl == 0); //if a unit is learnt, we should backtrack to dl 0...
        add_new_xlit( cls.get_unit(), -1, 0);
        return;
    }
    //now cls has at least two xlits, i.e., we can construct xcls_watch!

    // first convert cls to xcls_watch, then update with dl 0 units
    const var_t i = xclss.size();
    // add cls to xclss (and update watch_lists)
    init_and_add_xcls_watch( std::move(cls) );
    xclss[i].set_unit(assignments, dl_count, dl);
    VERB(65, "c new xclss "+xclss.back().to_str(assignments));
    xclss[i].update(alpha, alpha_dl, dl_count);
    assert( xclss.back().is_unit(dl_count) );

    // perform steps as in GCP case UNIT
    // NEW LIN-EQS
    xlit unit = xclss.back().get_unit();
    unit.reduce(assignments, assignments_dl, dl); //TODO we should also be able to use 'unit.reduce(assignments);'
    VERB(65, "new UNIT " + unit.to_str() + " with reason clause " + get_last_reason().to_str());
    // add to assignments and trail
    add_new_xlit(unit, i, dl);
    bump_score(unit);
    assert(assert_data_structs());
};

xlit new_unit;

//perform full GCP -- does not stop if conflict is found -- otherwise assert_data_struct will fail!
void solver::GCP(stats &s) {
    VERB(90, "GCP start");
    while(!gcp_queue.empty() && is_consistent()) {
        s.no_gcp++;
        // s.total_upd_xsys_size += get_latest_xsys().size();
        // update relevant xclsses
        const var_t upd_lt = gcp_queue.front();
        gcp_queue.pop();
        // for(const auto& [i,j] : upd_idxs) {
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
                assert(xclss[i].to_xcls().reduce(assignments).is_zero()); //in particular it must be zero when reduced with assignments!
                // IGNORE THIS CLAUSE FROM NOW ON
                decr_active_cls(xclss[i].get_inactive_lvl(dl_count));
                break;
            case xcls_upd_ret::UNIT: //includes UNSAT case (i.e. get_unit() reduces with assignments to 1 !)
                assert(xclss[i].is_unit(dl_count));
                assert(xclss[i].is_inactive(dl_count));
                assert(xclss[i].to_xcls().reduce(assignments).is_unit() || xclss[i].to_xcls().reduce(assignments).is_zero());
                //assert(xclss[i].is_inactive(alpha));
                // IGNORE THIS CLAUSE FROM NOW ON
                decr_active_cls(xclss[i].get_inactive_lvl(dl_count));
                // NEW LIN-EQS
                new_unit = std::move(xclss[i].get_unit());
                // add to assignments
                if( add_new_xlit(new_unit, i, xclss[i].get_inactive_lvl(dl_count)) ) {
                    assert(xclss[i].to_xcls().reduce(assignments).is_zero()); //in particular it must now be zero w.r.t. assignments (since new_unit has already been added!)
                    ++s.new_px_upd;
                    bump_score(new_unit); //TODO should we bump on propagation?! probably not!
                }
                if (!is_consistent()) { 
                    VERB(70, "UNSAT with conflict clause " + get_last_reason().to_str()); 
                    return; //quit propagation immediately at conflict!
                    }
                break;
            case xcls_upd_ret::NONE:
                //assert(xclss[i].is_none(alpha));
                assert(xclss[i].is_none(dl_count));
                assert(xclss[i].is_active(dl_count));
                //assert(xclss[i].is_active(alpha));
                //update watch-list!
                break;
            }
        }
    }
    VERB(90, to_str());
    VERB(90, "GCP end");
    assert(assert_data_structs());
};

// implementation of a dpll-solver
void solver::dpll_solve(stats &s) {
    VERB(25, "c dpll-solving start")
    // return UNSAT if linsys has no solution
    if (!is_consistent()) {
        s.sat = false;
        s.finished = true;
        return;
    }

    // current decision lvl
    dl = 0;
    dl_count[dl]++;

    // set update/fls/decH funcs
    dec_heu_t decH = &solver::dh_lex_LT;
    switch (opt.dh) {
    case dec_heu::vsids:
        decH = &solver::dh_vsids_UNFINISHED;
        break;
    case dec_heu::lwl:
        decH = &solver::dh_longest_wl;
        break;
    case dec_heu::lex:
        decH = &solver::dh_lex_LT;
        break;
    case dec_heu::swl:
        decH = &solver::dh_vsids_UNFINISHED;
        break;
    default:
        assert(false);
        break;
    }
    
    // stack for xsys that store alternative dec
    xsys new_xsys = xsys();
    std::stack<xsys> dec_stack;

    // update graph -- before making decisions!
    GCP(s);

    while (active_cls > 0 || !is_consistent()) {
        if (s.cancelled.load()) {
            VERB(10, "c cancelled");
            return;
        }
        // make decision / backtrack
        if (!is_consistent()) {
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
            //auto [lvl, learnt_cls] = (this->*analyze)();
            backtrack(dl-1);
            VERB(100, to_str());

            dec_stack.top().update(assignments, assignments_dl, dl);
            add_new_guess( dec_stack.top() ); //add as 'guess', i.e., trail and reason stacks are ill-managed here, but that is irrelevant since we do not use those in the dpll-type solver!
            VERB(100, to_str());
            // decay + bump scores of conflict clause!
            bump_score( dec_stack.top() );
            dec_stack.pop();
            decay_score();
            assert( is_consistent() == assignments[0].is_zero() );
            assert( assignments_xsys.is_consistent() == is_consistent() );
        } else {
            ++dl;
            ++dl_count[dl];
            ++s.no_dec;
            // save state
            save_state();

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

        // update graph
        GCP(s);

        assert((var_t)state_stack.size() == dl + 1);
        assert(assert_data_structs());
    }

    // solution can be deduced from assignments!
    // matrix corr to eqs in assignments is in upper triangular form, i.e., solve from 'back' to 'front'
    s.sol = vec<bool>(opt.num_vars, false);
    for (auto l = assignments.rbegin(); l != assignments.rend(); ++l)
        l->solve(s.sol);

    s.sat = true;
    s.finished = true;

    return;
};

//implementation of a cdcl-solver
void solver::cdcl_solve(stats &s) {
    VERB(25, "c cdcl-solving start")
    // return UNSAT if linsys has no solution
    if (!is_consistent()) {
        s.sat = false;
        s.finished = true;
        return;
    }

    // current decision lvl
    dl = 0;
    dl_count[dl]++;

    // set update/fls/decH funcs
    dec_heu_t decH = &solver::dh_lex_LT;
    switch (opt.dh) {
    case dec_heu::vsids:
        decH = &solver::dh_vsids_UNFINISHED;
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
    case ca_alg::no:
        analyze = &solver::analyze_dpll;
        break;
    case ca_alg::fuip:
        analyze = &solver::analyze_dpll;
        //analyze = &solver::analyze_exp;
        break;
    default: //should never be executed
        assert(false);
        break;
    }

    // stack for xsys that store alternative dec
    xsys new_xsys = xsys();

    // update graph -- before making decisions!
    GCP(s);

    while (active_cls > 0 || !is_consistent()) {
        if (s.cancelled.load()) {
            VERB(10, "c cancelled");
            return;
        }
        // make decision / backtrack
        if (!is_consistent()) {
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
            // backtrack

            ///// CLAUSE LEARNING /////
            auto [lvl, learnt_cls] = (this->*analyze)();
            // backtrack
            backtrack(lvl);
            VERB(100, to_str());

            // add learnt_cls
            add_learnt_cls( std::move(learnt_cls) );
            VERB(100, to_str());
            // decay + bump scores of conflict clause!
            bump_score(learnt_cls.get_ass_VS());
            decay_score();
            assert( is_consistent() == assignments[0].is_zero() );
        } else {
            ++dl;
            ++dl_count[dl];
            ++s.no_dec;
            // save state
            save_state();

            // make new decision!
            // use decisions heuristic to find next decision!
            std::pair<xsys, xsys> dec = (this->*decH)();
            VERB(25, "c " << std::to_string(dl) << " : "
                          << "decision " << std::to_string(s.no_dec) << " : " << std::to_string(dec.first.size()) << " or " << std::to_string(dec.second.size()) << " eqs")
            VERB(50, "c " << std::to_string(dl) << " : "
                          << "decision " << std::to_string(s.no_dec) << " namely [" << dec.first.to_str() << "] or [" << dec.second.to_str() << "]")
            add_new_guess(std::move(dec.first));
        }

        // update graph
        GCP(s);

        assert((var_t)state_stack.size() == dl + 1);
        assert(assert_data_structs());
    }

    // solution can be deduced from assignments!
    // matrix corr to eqs in assignments is in upper triangular form, i.e., solve from 'back' to 'front'
    s.sol = vec<bool>(opt.num_vars, false);
    for (auto l = assignments.rbegin(); l != assignments.rend(); ++l)
        l->solve(s.sol);

    s.sat = true;
    s.finished = true;

    return;
};


// overwrite to_str() func
std::string solver::to_str() const noexcept {
    // generate string of edges with lexicographic ordering!
    vec<std::string> str(xclss.size());
    // construct strings!
    auto to_str = [&](const xcls_watch &xcls) -> std::string { return xcls.to_str(assignments); };
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

#ifdef NDEBUG
    bool solver::assert_data_structs() const noexcept { return true; };
#else
    bool solver::assert_data_structs() const noexcept {
        //sanity check on assignments_dl
        for([[maybe_unused]] const auto lvl : assignments_dl) assert( lvl <= dl);
        for([[maybe_unused]] const auto lvl : alpha_dl) assert( lvl <= dl);

        // check data structs of xclss
        for (var_t i = 0; i < xclss.size(); i++) {
            assert(xclss[i].assert_data_struct());
            //only check advanced conditions if gcp_queue is empty!
            if(gcp_queue.empty()) assert(xclss[i].assert_data_struct(alpha,dl_count));
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
                for([[maybe_unused]] auto i : *it) { assert( assignments_watch[i].watches( idx ) ); }
                ++it; ++idx;
            }
        }

        // check that assignments_xsys and assignments agree!
        if(assignments_xsys != xsys(assignments) ) {
            VERB(100, "assignments_xsys: " + assignments_xsys.to_str());
            VERB(100, "xsys(assignments): " + xsys(assignments).to_str());
            xsys tmp = xsys(assignments);
        };
        assert(assignments_xsys == xsys(assignments) );


        // check that assignments in alpha are backed by assignment_xsys
        if(is_consistent()) {
            for([[maybe_unused]] const auto& [lt,idx] : assignments_xsys.get_pivot_poly_idx()) {
                if(assignments_xsys.get_xlits(idx).as_bool3() != alpha[lt] ) {
                    VERB(100, "assignments_xys.get_xlits(idx) = " + idx->to_str() );
                    VERB(100, "alpha[" + std::to_string(lt) + "] = " + b3_to_str( alpha[lt] ));
                }
                assert(assignments_xsys.get_xlits(idx).as_bool3() == alpha[lt]);
            }
        }

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


void solver::print_assignments(std::string lead) const noexcept {
  VERB(80, lead);
  VERB(80, lead+" assignments");
  VERB(80, lead+" lt dl ass");
  for(var_t i = 0; i<assignments.size(); ++i) {
      VERB(80, lead+" " + std::to_string(i) + " " + std::to_string(assignments_dl[i]) + " " + assignments[i].to_str());
  }
}


void solver::print_trail(std::string lead) const noexcept {
  VERB(80, lead);
  VERB(80, lead+" trail");
  VERB(80, lead+" pos dl unit");
  auto it = trail.begin();
  for(var_t i = 0; i<trail.size(); ++i) {
    const var_t t = *it;
    VERB(80, lead+" " + std::to_string(i) + " " + std::to_string(assignments_dl[t]) + " " + assignments[t].to_str());
    ++it;
  }
}