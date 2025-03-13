#pragma once

#include <set>
#include <sstream>
#include <algorithm>

#include "misc.hpp"

#include "lineral.hpp"
#include "lineral_watch.hpp"
#include "lin_sys.hpp"

#include "cryptominisat/src/varreplacer.h"
#include "cryptominisat/src/solver.h"
#include "cryptominisat/src/gaussian.h"

#undef DEBUG_SLOW
#undef DEBUG_SLOWER

// #define DEBUG_SLOW
// #define DEBUG_SLOWER

static CMSat::vector<unsigned> xor_clause;

class lin_sys_lazy_GE
{
  private:
    /**
     * @brief cryptominisat SAT solver; used for efficient lazy Gauss-Jordan Elimination
     * @note it would be better to only use the code that is actually required (PropEngine::gauss_jordan_elim), but it depends on soo many other classes, that it is just much simpler to embed the 'whole' SAT solver and equip it only with the linerals for propagation...
     */
    CMSat::Solver* cms;
    CMSat::SolverConf conf;
    std::atomic<bool>* must_inter;
    var_t num_vars;

    /**
     * @brief linerals in lin_sys
     */
    lin_sys linerals;

    /**
     * @brief assigning linerals (literals), not yet fetched
     */
    list<lineral> implied_literal_queue;

    /**
     * @brief adds new alpha assignment to internal queue
     * 
     * @param var variable that is assigned
     * @param val value it is assigned to
     * @return true iff values is not yet assigned
     */
    bool enqueue_new_assignment(const var_t var, const bool val) {
        CMSat::Lit lit(var, val);
        const auto lit_replaced = cms->varReplacer->get_lit_replaced_with_outer(lit);
        if(lit!=lit_replaced) {
            //binary XOR/EQUIV propagates!
            lineral_vars.clear();
            lineral_vars.emplace_back( var );
            lineral_vars.emplace_back( lit_replaced.var() );
            implied_literal_queue.emplace_back( lineral_vars,  val^lit_replaced.sign(), presorted::no );
        }
        if(cms->value(lit_replaced.var()) == CMSat::l_Undef) {
            cms->enqueue<false>(lit_replaced);
            return true;
        } else {
            //ensure that value is correctly assigned in cms
            //assert( (var==0) || (cms->value(var) == (val ? CMSat::l_False : CMSat::l_True)) );
            return false;
        }
    }

    /**
     * @brief initialises lin_sys_watch, fixes second watches
     * @note after init use propagate() to finish initialization
     * 
     * @param alpha current alpha-assignment
     */
    var_t init_and_propagate(const vec<bool3>& alpha) {
        //set gaussconf settings -- copied from 'set_allow_otf_gauss()' in cryptominisat.cpp
        //conf.doFindXors = true;
        //conf.allow_elim_xor_vars = false;
        //conf.gaussconf.max_num_matrices = 10;
        //conf.gaussconf.max_matrix_columns = 10000000;
        //conf.gaussconf.max_matrix_rows = 10000;
        //conf.gaussconf.autodisable = false;
        //conf.xor_detach_reattach = true;
        //conf.allow_elim_xor_vars = false;

        conf.doFindXors = true;
        conf.allow_elim_xor_vars = false;
        conf.gaussconf.autodisable = false;
        conf.gaussconf.max_matrix_columns = 1000;
        conf.gaussconf.max_matrix_rows = 10000;
        conf.gaussconf.min_matrix_rows = 0;
        conf.gaussconf.max_num_matrices = 1000;
        conf.gaussconf.doMatrixFind = true;
        conf.gaussconf.min_gauss_xor_clauses = 0;
        conf.gaussconf.max_gauss_xor_clauses = 500000;
        conf.verbosity = 0;

        must_inter = new std::atomic<bool>();
        cms = new CMSat::Solver(&conf, must_inter);
        
        //compute num_vars and add new vars to cms
        if(num_vars==(var_t)-1) {
            num_vars = 0;
            for(const auto& l : linerals.get_linerals()) if(!l.is_constant()) num_vars = std::max(num_vars, l.get_idxs_()[l.size()-1]);
        }
        cms->new_vars( num_vars+1 );

        //add dummy clause in 0th variable -- this ensures CMSat::CNF is properly initialized (and can be deleted as well)
        cms->add_clause_outside({CMSat::Lit(0, false)});

        //push non-assigning linerals to solver all others just enqueue!
        list<const lineral*> linerals_assigning;
        //vec<CMSat::Lit> assignments;
        for(const auto& l : linerals.get_linerals()) {
            if(l.is_zero()) continue;
            if(!l.is_assigning()) {
                xor_clause.clear(); xor_clause.reserve( l.size() );
                for(const auto& i : l.get_idxs_()) xor_clause.emplace_back(i);
                cms->add_xor_clause_outside( xor_clause, l.has_constant() );
            } else {
                //assignments.clear();
                //assignments.emplace_back( l.LT(), l.has_constant() );
                //cms->add_clause_outside(assignments);
                linerals_assigning.push_back( &l );
            }
        }
        ////without this it is faster!
        //const std::string strategy = "must-scc-vrepl";
        //cms->simplify_with_assumptions(nullptr, &strategy);
        cms->find_and_init_all_matrices();

        for(const auto lp : linerals_assigning) {
            if(!alpha.empty() && alpha[lp->LT()]!=bool3::None) {
                continue; //skip already assigned variables
            }
            implied_literal_queue.emplace_back( *lp );
            if(!lp->is_one()) enqueue_new_assignment(lp->LT(), lp->has_constant());
        }

        #ifdef DEBUG_SLOW
            lin_sys sys_recv( get_recovered_linerals() );
            //NOTE we might not recover ALL linerals, because (1) propagation can 'destroy them', and (2) binary clauses are not recovered at all!
            for(const auto& l : sys_recv.get_linerals()) assert( linerals.reduce(l).is_zero() );
        #endif

        ////get all forced assignments
        //for(var_t i = 1; i<=num_vars; ++i) {
        //    if((alpha.empty() || alpha[i]==bool3::None)) {
        //        //implied_literal_queue.emplace_back( vec<var_t>({i}), cms->value(i)!=CMSat::l_True, presorted::no );
        //        auto lit = cms->varReplacer->get_lit_replaced_with_outer( CMSat::Lit(i, cm->) );
        //        if(cms->value(lit.var()) != CMSat::l_Undef) {
        //            implied_literal_queue.emplace_back( vec<var_t>({i}), cms->value(lit.var())!=CMSat::l_True, presorted::no );
        //            assert_slow( sys.reduce(implied_literal_queue.back()).is_zero() );
        //        }
        //    }
        //}

        var_t ct = propagate(alpha);

        //slows down overall solving!
        //collect all binary xors:
        for(auto& [l1,l2] : cms->get_all_binary_xors()) {
            implied_literal_queue.emplace_back( vec<var_t>({l1.var(), l2.var()}), l1.sign()^l2.sign(), presorted::no );
            ++ct;
        }

        //add 'conflict' if cms->okay() is false
        if(!cms->okay()) {
            implied_literal_queue.emplace_front( cnst::one );
            ++ct;
        }

        return ct;
    }

    vec<var_t> lineral_vars;
    lineral confl_to_lineral(CMSat::PropBy confl) {
        lineral_vars.clear();

        //find matrix and row responsible for propagation
        assert( confl.getType()==CMSat::xor_t || confl.getType()==CMSat::binary_t || confl.getType()==CMSat::clause_t  );
        switch(confl.getType()) {
            case CMSat::xor_t:
            {
                //find (and construct) corresponding lineral
                int32_t tmp_ID; //required for call to get_reasons -- irrelevant for us!
                auto xor_reason = cms->get_xor_reason_xorricane(confl, tmp_ID);

                assert( std::is_sorted(xor_reason->vars.begin(), xor_reason->vars.end()) );
                std::copy( xor_reason->begin(), xor_reason->end(), std::back_inserter(lineral_vars) );
                return lineral( lineral_vars, xor_reason->rhs, presorted::yes );
            }
            case CMSat::clause_t:
            {
                assert(false);
                CMSat::Clause const* cl = cms->cl_alloc.ptr(confl.get_offset());

                bool sign = true;
                for(const auto& l : *cl) {
                    sign ^= l.sign();
                    lineral_vars.emplace_back( l.var() );
                }
                return lineral( lineral_vars, sign, presorted::no );
            }
            case CMSat::binary_t:
            {
                lineral_vars.emplace_back( cms->failBinLit.var() );
                lineral_vars.emplace_back( confl.lit2().var() );
                return lineral( lineral_vars, cms->failBinLit.sign()^!confl.lit2().sign(), presorted::no );
            }
            default:
                assert(false);
        }
        return lineral(cnst::one);
    }

    lineral CMS_reason_to_lineral(CMSat::Lit trail_el) {
        lineral_vars.clear();

        //find matrix and row responsible for propagation
        const CMSat::VarData& v_data = cms->varData[trail_el.var()];
        assert( v_data.reason.getType()==CMSat::xor_t || v_data.reason.getType()==CMSat::binary_t || v_data.reason.getType()==CMSat::clause_t  );
        switch(v_data.reason.getType()) {
            case CMSat::xor_t:
            {
                //find (and construct) corresponding lineral
                int32_t tmp_ID; //required for call to get_reasons -- irrelevant for us!
                auto xor_reason = cms->get_xor_reason_xorricane(v_data.reason, tmp_ID);

                assert( std::is_sorted(xor_reason->vars.begin(), xor_reason->vars.end()) );
                std::copy( xor_reason->begin(), xor_reason->end(), std::back_inserter(lineral_vars) );
                return lineral( lineral_vars, xor_reason->rhs, presorted::yes );
            }
            case CMSat::clause_t:
            {
                assert(false);
                CMSat::Clause const* cl = cms->cl_alloc.ptr(v_data.reason.get_offset());

                bool sign = true;
                for(const auto& l : *cl) {
                    sign ^= l.sign();
                    lineral_vars.emplace_back( l.var() );
                    assert(l.var() < cms->nVars());
                }
                return lineral( lineral_vars, sign, presorted::no );
            }
            case CMSat::binary_t:
            {
                lineral_vars.emplace_back( trail_el.var() );
                lineral_vars.emplace_back( v_data.reason.lit2().var() );
                return lineral( lineral_vars, trail_el.sign()^!v_data.reason.lit2().sign(), presorted::no );
            }
            default:
                assert(false);
        }
        return lineral(cnst::one);
    }

    //store linerals implying clash_variables -- as soon as we have 
    std::map<var_t,lineral> clash_var_to_reason;
    /**
     * @brief propagate all enqueued decisions and updates implied_literal_queue appropriately
     * 
     * @param alpha current alpha-assignments
     * 
     * @return number of new alpha assignments
     */
    var_t propagate(const vec<bool3>& alpha) {
        #ifdef DEBUG_SLOWER
            //add all decisions to L
            lin_sys L = linerals;
            lin_sys L_dec;
            for(var_t i = 0; i<alpha.size(); ++i) {
              if(alpha[i]!=bool3::None) L_dec.add_lineral( lineral(i, b3_to_bool(alpha[i])) );
            }
            // find all uniquely determined alpha
            L += L_dec;
            vec<lineral> det_alpha;
            for(const auto& lin : L.get_linerals()) {
              if(lin.is_assigning() && !L_dec.reduce(lin).is_zero()) det_alpha.emplace_back( lin );
            }
            lin_sys L_det( det_alpha );
            std::cout << "c " << BLUE("LGJ should deduce: " << L_det.to_str()) << std::endl;
        #endif

        //propagate with CMS and read propagations from trail
        const auto trail_size_prev = cms->trail_size();
        CMSat::PropBy confl = cms->propagate<false>();
        
        #ifdef DEBUG_SLOWER
            if(L_det.dim()>0) { //only print when there is anything to deduce...
                std::cout << "linerals (reduced) : ";
                for(const auto& l: linerals.get_linerals()) std::cout << l.to_str() << " ";
            }
        #endif

        //iterate over new elements in trail
        CMSat::Lit trail_el;
        for(size_t trail_pos = trail_size_prev; trail_pos<cms->trail_size(); ++trail_pos) {
            trail_el = cms->trail_at(trail_pos);

            if(alpha.size()>0 && alpha[trail_el.var()]!=bool3::None) {
                continue; //skip already assigned variables
            }

            lineral lin = CMS_reason_to_lineral(trail_el);

            #ifdef DEBUG_SLOW
                //ensure that lin is implied by linerals
                assert( linerals.reduce(lin).is_zero() );
            #endif

            assert(lin.get_idxs_().back()<=num_vars);
            implied_literal_queue.emplace_back( std::move(lin) );

            //if(trail_el.var()>num_vars) {
            //    //this is a clash variable -- store the reason clause for later!
            //    clash_var_to_reason[trail_el.var()] = std::move(lin);
            //} else {
            //    //a regular variable was implied; i.e. all its occuring clash variables must already be assigned
            //    //thus we must reasons for them and the original lineral can be reconstructed!
            //    //NOTE clash variables come last, i.e., there is a clash variable in lin iff the last one is a clash var!
            //    while(!lin.get_idxs_().empty() && lin.get_idxs_().back()>num_vars) {
            //        const auto v = lin.get_idxs_().back();
            //        if(clash_var_to_reason.find(v)!=clash_var_to_reason.end()) {
            //            lin += clash_var_to_reason[v];
            //        }
            //    }
            //    assert( lin.get_idxs_().empty() || lin.get_idxs_().back()<=num_vars );

            //    #ifdef DEBUG_SLOW
            //        //ensure that lin is implied by linerals
            //        assert( sys.reduce(lin).is_zero() );
            //    #endif

            //    implied_literal_queue.emplace_back( std::move(lin) );
            //}
        }

        //if we have a conflict, this corresponding PropBy is not found on trail, i.e., treat it now!
        //(this has to be done ATER all other clauses are put in the queue s.t. confl is actually a conflict under the previously implied assignments)
        if(!confl.isnullptr()) {
            //we have a conflict!
            cms->ok = false;
            lineral lin = confl_to_lineral(confl);
            assert( lin.get_idxs_().back()<=num_vars );
            implied_literal_queue.emplace_back( std::move(lin) );

            ////remove possible clash variables from lin
            //while(!lin.get_idxs_().empty() && lin.get_idxs_().back()>num_vars) {
            //    const auto v = lin.get_idxs_().back();
            //    if(clash_var_to_reason.find(v)!=clash_var_to_reason.end()) {
            //        lin += clash_var_to_reason[v];
            //    }
            //}
            //assert( lin.get_idxs_().empty() || lin.get_idxs_().back()<=num_vars );

            //#ifdef DEBUG_SLOW
            //    //ensure that lin is implied by linerals
            //    assert( sys.reduce(lin).is_zero() );
            //#endif

            //implied_literal_queue.emplace_back( std::move(lin) );
        }

        #ifdef DEBUG_SLOWER
            //ensure that all alpha-assignments are reflected correctly in cms!
            //assert( check_cms_assignments(alpha) ); // skip this check -- until I have a better understanding of how CMS works!

            //check we got all possible implications!
            lin_sys L2( implied_literal_queue );
            L2 += L_dec;
            vec<lineral> det_alpha2;
            for(const auto& lin : L2.get_linerals()) {
              if(lin.is_assigning() && !L_dec.reduce(lin).is_zero()) det_alpha2.emplace_back( lin );
            }
            lin_sys L_det2( det_alpha2 );
            //we might miss conflicts here due to binary clauses/equivalent xors missing in the matrices!
            std::cout << "c " << BLUE("LGJ could deduce:  " << L_det2.to_str()) << std::endl;
            if( L_det.to_str() != L_det2.to_str() ) {
                std::cout << "c " << RED("WARNING") << BLUE(" LGJ deduction incomplete!") << std::endl;
            }
        #endif

      
        return implied_literal_queue.size();
    }

  public:
    lin_sys_lazy_GE() {};
    
    lin_sys_lazy_GE(lin_sys&& sys, const var_t _num_vars) noexcept : num_vars(_num_vars), linerals(sys) {
        vec<bool3> alpha;
        init_and_propagate(alpha);
    };

    lin_sys_lazy_GE(const vec<lineral>& linerals_, const var_t _num_vars = (var_t) -1) noexcept :  num_vars(_num_vars), linerals(linerals_) {
        vec<bool3> alpha;
        init_and_propagate(alpha);
    };

    ~lin_sys_lazy_GE() {
        delete cms;
        delete must_inter;
    };

    /**
     * @brief Returns reason lineral for given var
     * 
     * @param var that is assigned by linerals under the current assignments
     * @return lineral which is the reason for the assignment of var
     */
    lineral get_reason(var_t var) {
        assert( cms->varData[var].propagated );
        assert( !cms->varData[var].reason.isnullptr() );

        CMSat::Lit lit = CMSat::Lit(var, cms->value(var) == CMSat::l_False);
        return CMS_reason_to_lineral(lit);
    }

    list<lineral>& get_implied_literal_queue() { return implied_literal_queue; }
    void clear_implied_literal_queue() { implied_literal_queue.clear(); }

    const list<lineral>& get_linerals() const { return linerals.get_linerals(); }
    
    /**
     * @brief checks whether the assignments of cms are correct
     * 
     * @param alpha current alpha assignments
     * @return true iff internal CMS is compatible with alpha
     */
    bool check_cms_assignments(const vec<bool3>& alpha) const {
        for(var_t i = 1; i<alpha.size(); ++i) {
            if( alpha[i]!=bool3::None && cms->value(i)!=(b3_to_bool(alpha[i]) ? CMSat::l_False : CMSat::l_True) ) {
                return false;
            }
        }
        return true;
    }

    /**
     * @brief assigns var, i.e., ensures it is not watched, and fixes row-echelon under alpha
     * 
     * @param var newly assigned variable
     * @param alpha current alpha-assignment
     * @return bool true iff (var is newly assigned and new alpha assignments were deduced) or queue still has implications to be fetched
     */
    bool assign(const var_t var, const vec<bool3>& alpha, var_t dl) {
        assert(implied_literal_queue.empty());
        //backtrack or create new dl
        if(cms->decisionLevel()>dl) backtrack(dl);
        if(cms->decisionLevel()<dl) cms->new_decision_level();
        assert( cms->decisionLevel()==dl );

        //add assignment to linerals if dl==0
        if( dl==0 ) {
            linerals.add_lineral( lineral(var, b3_to_bool(alpha[var])) );
        }

        //enqueue assignment and propagate if var is not yet assigned in cms
        if( enqueue_new_assignment(var, b3_to_bool(alpha[var])) ) {
            propagate(alpha);
        }
        
        return !implied_literal_queue.empty();
    }
    
    /**
     * @brief add new lineral to lazy lin sys
     * @note may only be used at dl 0 (!)
     * 
     * @param l lineral to be added
     * @param alpha current alpha-assignments
     * @return var_t number of implied new alpha assignments
     */
    inline var_t add_lineral(lineral&& l, const vec<bool3>& alpha) {
      return add_linerals({std::move(l)}, alpha);
    }

    /**
     * @brief add new lineral to lazy lin sys
     * @note may only be used at dl 0 (!)
     * 
     * @param ls list of linerals to be added
     * @param alpha current alpha-assignments
     * @return var_t number of new alpha assignments
     */
    var_t add_linerals(vec<lineral>&& ls, const vec<bool3>& alpha) {
        //BEWARE: not sure how to add linerals without destroying some internal structure in cms!
        //        old code trying this can be found below - for now we just re-init the whole thing!

        assert(cms->decisionLevel() == 0);
        if(ls.empty()) return 0;

        delete cms;
        delete must_inter;

        //add new linerals
        lin_sys new_lins(std::move(ls));
        linerals += new_lins;

        //re-init object
        return init_and_propagate(alpha);

        /////// OLD CODE //////
        //assert(cms->decisionLevel() == 0);
        //if(ls.empty()) return 0;

        ////proceed as follows: add linerals, rebuild gauss matrices, then propagate
        //cms->clear_gauss_matrices(false); //bool decides whether data for matrices is de-allocated!

        ////add new linerals
        //auto it = linerals.insert(linerals.end(), make_move_iterator(ls.begin()), make_move_iterator(ls.end()));

        ////push non-assigning linerals to solver all others just enqueue!
        //list<const lineral*> linerals_assigning;
        //for(;it != linerals.end(); ++it) {
        //    const auto& l = *it;
        //    if(l.is_zero()) continue;
        //    if(!l.is_assigning()) {
        //        xor_clause.clear(); xor_clause.reserve( l.size() );
        //        for(const auto& i : l.get_idxs_()) xor_clause.emplace_back(i);
        //        cms->add_xor_clause_outside( xor_clause, l.has_constant() );
        //    } else {
        //        linerals_assigning.push_back( &l );
        //    }
        //}
        //cms->xorclauses_updated = true;
        
        ////re-init matrices + propagate
        //cms->find_and_init_all_matrices();

        //for(const auto lp : linerals_assigning) {
        //    implied_literal_queue.emplace_back( *lp );
        //    if(!lp->is_one()) enqueue_new_assignment(lp->LT(), lp->has_constant());
        //}

        //return propagate(alpha);
    }

    void backtrack(var_t lvl) {
        ////go through trail of cms and remove all the lineral reasons for the clash variables!
        //auto trail_pos = cms->trail_size()>0 ? (cms->trail_size())-1, : 0;
        //while(cms->varData[ cms->trail_at(trail_pos).var() ].level > lvl) {
        //    const auto var = cms->trail_at(trail_pos).var();
        //    if(var > num_vars) {
        //        //this is a clash variable -- remove the reason clause for it!
        //        clash_var_to_reason.erase(var);
        //    }
        //    --trail_pos;
        //}

        cms->cancelUntil<false, true>(lvl);
        assert(cms->decisionLevel() == lvl);
        implied_literal_queue.clear();
    }

    
    vec<lineral> get_recovered_linerals() const {
        vec<lineral> lins;
        vec<var_t> vars;
        for(var_t row=0; row<cms->gmatrices.size(); ++row) {
            for(const auto& x : cms->gmatrices[row]->xorclauses) {
                //parse xor to lineral
                vars.clear();
                for(const auto& v : x.vars) vars.emplace_back( v );
                lins.push_back( lineral(vars, x.rhs, presorted::no) );
            }
        }
        return lins;

        ////this messes up data structures!!
        //cms->start_getting_constraints(true,false);
        //vector<CMSat::Lit> lits;
        //bool is_xor; bool rhs;
        //vec<var_t> vars;
        //while ( cms->get_next_constraint(lits, is_xor, rhs) ) {
        //    if (!is_xor) continue;
        //    //parse xor to lineral
        //    vars.clear();
        //    for(const auto& x : lits) vars.emplace_back( x.var() );
        //    lins.push_back( lineral(vars, rhs, presorted::no) );
        //}
        //cms->end_getting_constraints();
        //return lins;
    }

    var_t size() const { return linerals.size(); };

    std::string to_str() const;
};
