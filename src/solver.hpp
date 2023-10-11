#pragma once

#include <stack>
#include <math.h>
#include <map>
#include <list>
#include <queue>
#include <memory>
#include <array>

#include "solve.hpp"
#include "misc.hpp"
#include "xlit/xlit.hpp"
#include "xlit/xlit_watch.hpp"
#include "xlit/xsys.hpp"
#include "xlit/xcls.hpp"
#include "xlit/xcls_watch.hpp"

#define TRAIL trails.back()

//#define EXACT_UNIT_TRACKING

struct state_repr {
  /**
   * @brief number of active clauses
   */
  var_t active_cls;

#ifdef EXACT_UNIT_TRACKING
  /**
   * @brief current (non)-constant assignments
   * @todo remove!
   */
  xsys L;

  state_repr(const var_t _active_cls, const xsys& _L) : active_cls(_active_cls), L(_L) {};
#else
  state_repr(const var_t _active_cls) : active_cls(_active_cls) {};
#endif

};

enum class trail_t { EQUIV, IMPLIED_UNIT, IMPLIED_ALPHA, LINERAL_IMPLIED_ALPHA, LEARNT_UNIT, GUESS };

struct trail_elem {
  var_t ind;
  trail_t type;
  var_t rs_cls_idx;

  trail_elem() : ind(0), type(trail_t::IMPLIED_UNIT), rs_cls_idx(-1) {};
  trail_elem(const var_t& _ind, const trail_t& _type, const var_t& _rs) : ind(_ind), type(_type), rs_cls_idx(_rs) {};
  trail_elem(const trail_elem& other) : ind(other.ind), type(other.type), rs_cls_idx(other.rs_cls_idx) {};
  trail_elem(trail_elem&& other) : ind(other.ind), type(other.type), rs_cls_idx(other.rs_cls_idx) {};
};

struct lineral_queue_elem {
  xlit lin;
  trail_t type;
  var_t rs_cls_idx;
  var_t lvl;

  lineral_queue_elem() : lin(), type(trail_t::IMPLIED_ALPHA), rs_cls_idx(-1), lvl(-1) {};
  lineral_queue_elem(const xlit& _lin, const var_t& _rs, const trail_t& _type, const var_t& _lvl) : lin(_lin), type(_type), rs_cls_idx(_rs), lvl(_lvl) {};
  lineral_queue_elem(const lineral_queue_elem& other) : lin(other.lin), type(other.type), rs_cls_idx(other.rs_cls_idx), lvl(other.lvl) {};
  lineral_queue_elem(lineral_queue_elem&& other) : lin(other.lin), type(other.type), rs_cls_idx(other.rs_cls_idx), lvl(other.lvl) {}; 
};


class solver
{
  private:
    /**
     * @brief xor-clause watchers
     */
    vec< xcls_watch > xclss;

    /**
     * @brief utility[i] gives number of unit propagations of xclss[i] (with moving average)
     */
    vec<var_t> utility;
    const var_t util_cutoff = 5; //min utility to keep a clause on cleanup
    const var_t restart_schedule = 2<<12; //number of conflicts between cleanups

    /**
     * @brief watch_list[i] contains all idxs j s.t. xclss[j] watches indet i
     */
    vec< std::list<var_t> > watch_list;
    
    /**
     * @brief TODO
     */
    vec< std::list< std::array<var_t,4> > > L_watch_list;

    /**
     * @brief options for heuristics of dpll-solver (and more)
     */
    options opt;

    /**
     * @brief current decision level
     */
    var_t dl;

    /**
     * @brief number of active clauses
     */
    var_t active_cls;

    /**
     * @brief stack of state repr -- used for backtracking (and for dl-wise update of learnt-clauses)
     */
    vec<state_repr> state_stack;
    
    /**
     * @brief 'activity' of each variable; used for decision heuristic
     * @note entries must be strictly positive! (otherwise max_path/max_tree might fail!)
     */
    vec<unsigned int> activity_score;
    const unsigned int bump = 1;
    const float decay = 0.9;

    /**
     * @brief checks 
     * 
     * @return true if current state is at conflict
     */
    inline bool no_conflict() const { return alpha[0]!=bool3::True; };

    //CDCL vars
    /**
     * @brief counts how often a dl was visited -- required to quickly discard xlit that were already watched previously in the current search tree
     *        dl_count[i] is the number of times the solver was at dl i (counting once after increasing dl and before decreasing dl)
     */
    vec<dl_c_t> dl_count;

#ifdef EXACT_UNIT_TRACKING
    /**
     * @brief current assignments of vars; assignments[i] contains xlit with LT i
     */
    vec< xlit > assignments;
#endif
    
    /**
     * @brief current unit watches
     * @note lineral_watches[lvl] contains all units added in dl lvl; used as stack
     */
    vec< vec< xlit_watch > > lineral_watches;
    //TODO change to vec< std::list< xlit_watch> > lineral_watches; (!)
    //should allow us to access contents more quickly!

    /**
     * @brief assignments_list[lt] contains all assignments with leading term lt
     */
    //vec< std::list< std::array<var_t,4> > > assignments_list;

#ifdef EXACT_UNIT_TRACKING
    /**
     * @brief current assignments -- stored as xsys
     */
    xsys assignments_xsys;
#endif
    
    /**
     * @brief current assignments of vars; assignments[i] contains xlit with LT i
     */
    vec< bool3 > alpha;
    
    /**
     * @brief phase of last assignment - phase saving
     */
    vec< bool3 > last_phase;

    /**
     * @brief dl of chosen/implied alpha assignments; i was true/false-decided at dl alpha_dl[i]
     */
    vec<var_t> alpha_dl;
    
    /**
     * @brief alpha_trail_pos[i] indicates the position of the alpha-assignment in trails[alpha_dl[i]]
     * 
     */
    vec<var_t> alpha_trail_pos;

#ifdef EXACT_UNIT_TRACKING
    /**
     * @brief dl of chosen assignments; i was assigned at dl assignments_dl[i]
     */
    vec<var_t> assignments_dl;
#endif

    /**
     * @brief if equiv_lits[i].ind is non-zero, i is congruent to equiv_lits[i].ind + (equiv_lits[i].polarity ? 1 : 0).
     * @note we must have i < equiv_lits[i].first
     */
    vec<equivalence> equiv_lits;
    
    /**
     * @brief dl info when equivalents were added
     */
    vec<var_t> equiv_lits_dl;

    /**
     * @brief trail of decisions/unit-propagations
     * @note trail[lvl] is the trail at level lvl
     */
    vec< std::list<trail_elem> > trails;

    std::deque<lineral_queue_elem> lineral_queue;
    
    xcls get_last_reason() const;

    std::pair<var_t,xcls_watch> analyze();
    std::pair<var_t,xcls_watch> analyze_exp();
    std::pair<var_t,xcls_watch> analyze_no_sres();
    std::pair<var_t,xcls_watch> analyze_dpll();

    inline void add_learnt_cls(xcls_watch&& cls) {
        assert(lineral_queue.empty());
        if(cls.deg()>=2) {
            const var_t i = add_xcls_watch( std::move(cls), true, true );
            assert(xclss[i].get_assigning_lvl() == dl); //ensure we did backtrack as far as possible!
            //assert(xclss[i].get_inactive_lvl(dl_count) == dl); //ensure we did backtrack as far as possible!
            utility[i]++;
        } else {
            assert(cls.deg()==1);
            add_new_lineral( cls.get_unit() );
            queue_implied_lineral( cls.get_unit(), lineral_watches[0].size()-1, trail_t::LEARNT_UNIT );
        }
    }


    //saves the phase of the TRAIL in last_phase according to selected phase_option
    inline void save_phase() {
      switch (opt.po) {
      case phase_opt::rand:
        //last_phase[trail.back()] = (bool)(rand() > (RAND_MAX/2)) ?  bool3::True : bool3::False;
        last_phase[TRAIL.back().ind] = alpha[TRAIL.back().ind];
        break;
      case phase_opt::save:
        last_phase[TRAIL.back().ind] = alpha[TRAIL.back().ind];
        break;
      case phase_opt::save_inv:
        last_phase[TRAIL.back().ind] = alpha[TRAIL.back().ind] == bool3::True ? bool3::False : bool3::True;
        break;
      }
    }

    inline bool pop_trail() noexcept {
      if (TRAIL.empty()) return false;
      //check if assignments or only alpha needs to be cleared!
#ifdef EXACT_UNIT_TRACKING
      if(alpha_dl[TRAIL.back().ind] <= assignments_dl[TRAIL.back().ind]) {
        //clear assignments_dl
        assignments[TRAIL.back().ind] = xlit();
        assignments_dl[TRAIL.back().ind] = (var_t) -1;
      }
#endif
      //store last_phase
      switch(TRAIL.back().type) {
      case trail_t::GUESS:
      case trail_t::IMPLIED_UNIT:
        assert(lineral_watches[dl].back().LT() == TRAIL.back().ind);
        lineral_watches[dl].pop_back(); //remove unit
        assert(!lineral_watches.empty());
        break;
      case trail_t::LEARNT_UNIT:
      case trail_t::LINERAL_IMPLIED_ALPHA:
      case trail_t::IMPLIED_ALPHA:
        save_phase();
        alpha[TRAIL.back().ind] = bool3::None;
        alpha_dl[TRAIL.back().ind] = (var_t) -1;
        alpha_trail_pos[TRAIL.back().ind] = (var_t) -1;
        break;
      case trail_t::EQUIV:
    #ifdef USE_EQUIV
        equiv_lits[TRAIL.back().ind].clear();
        equiv_lits_dl[TRAIL.back().ind] = (var_t) -1;
    #endif
        break;
      }
      TRAIL.pop_back();
      return true;
    }


    typedef std::pair<xsys,xsys> (solver::*dec_heu_t)() const;
    typedef std::pair<var_t,xcls_watch> (solver::*ca_t)();

    void bump_score(const var_t& ind);
    void bump_score(const xsys& new_xsys);
    void bump_score(const xlit& lit);
    void decay_score();

    inline void add_new_guess(const xsys& L) {
      //update assignments
      for(const auto& [lt,idx] : L.get_pivot_poly_idx()) {
        queue_implied_lineral(*idx, -1, trail_t::GUESS);
      };
    };

    /**
     * @brief decrease active_cls by one -- starting at dl lvl
     * 
     * @param idx of xcls that became inactive
     */
    inline void decr_active_cls(const var_t& idx) {
      if(!xclss[idx].is_irredundant()) return;
      //update curr val
      --active_cls;
      //update vals in state_stack
      for(var_t j = xclss[idx].get_inactive_lvl(dl_count)+1; j<state_stack.size(); ++j) --state_stack[j].active_cls;
    }

    xlit _reduced_lit;
    /**
     * @brief adds new xlit to data structure if deduced at current dl; also reduces with current assignments to find new true/false assignments
     * 
     * @param lit literal to be added
     * @param rs idx of reason_UNIT clause
     * 
     * @return var_t ind>=0 iff alpha[ind] is now assigned; ind==-1 means no new alpha-assignment
     */
    inline var_t add_implied_lineral(const xlit& lit, const var_t& rs, const trail_t type = trail_t::IMPLIED_UNIT, const var_t _lvl = -1) {
      const var_t lvl = _lvl == (var_t) -1 ? dl : _lvl;
      _reduced_lit = lit;
      _reduced_lit.reduce(alpha,alpha_dl,lvl); //reduce with alpha assignments -- the least we should do!
      if(!_reduced_lit.is_assigning()) {
        _reduced_lit.reduce(equiv_lits,equiv_lits_dl,lvl); //reduce equivalent variable
      }
  #ifdef EXACT_UNIT_TRACKING
      if(!_reduced_lit.is_assigning()) {
        _reduced_lit.reduce(assignments, assignments_dl, dl); //reduce with assignments AND alpha...
      }
  #endif
      if(_reduced_lit.is_zero()) return -1; 
      VERB(65, "c " + std::to_string(lvl) + " : new UNIT " + lit.to_str() + " ~> " + _reduced_lit.to_str() + (type!=trail_t::LINERAL_IMPLIED_ALPHA && type!=trail_t::LEARNT_UNIT ? (rs<xclss.size() ? " with reason clause " + xclss[rs].to_str() : "") : (" with reason clause " + lineral_watches[0][rs].to_str()) ) );
      
      const var_t lt = _reduced_lit.LT();
      //TODO should we always reduce?! consider the following:
      //we already have UNIT x1+x2+x3 and now get x1; as of now, we add x2+x3, even though x1 would be assigning!
      //DO NOT REDUCE WITH TOO LONG XORs otherwise it might blow up!
      // add to trail //TODO add in propoer position in trail!

#ifdef EXACT_UNIT_TRACKING
      // update assignments
      assert(assignments[lt].is_zero() || _reduced_lit == assignments[lt]);
      if(assignments[lt].is_zero()) {
        assignments[lt] = _reduced_lit;
        assignments_dl[lt] = dl;
      }
      //add _reduced_lit to assignments_xsys
      assert((var_t)state_stack.size() >= dl);
      for(auto i = dl+1; i < (var_t) state_stack.size(); ++i) {
        state_stack[i].L += xsys(_reduced_lit);
      }
      assignments_xsys += xsys(_reduced_lit);
#endif

      if(type!=trail_t::IMPLIED_ALPHA && type!=trail_t::LINERAL_IMPLIED_ALPHA && type!=trail_t::LEARNT_UNIT) {
        trails[lvl].emplace_back( lt, type, rs);
        const auto& l = lineral_watches[lvl].emplace_back( std::move(_reduced_lit), alpha, alpha_dl, lvl, dl_count, rs );
        assert( l.is_active(dl_count) );
        // add to L_watch_list's -- if there is anything to watch
        if(l.size()>0) {
          L_watch_list[ l.get_wl0() ].emplace_back( std::array<var_t,4>({lvl, (var_t) (lineral_watches[lvl].size()-1), lvl, dl_count[lvl]}) );
          if(l.get_wl0() != l.get_wl1()) L_watch_list[ l.get_wl1() ].emplace_back( std::array<var_t,4>({lvl, (var_t) (lineral_watches[lvl].size()-1), lvl, dl_count[lvl]}) );
        }
        //assignments_list[lt].emplace_back( std::array<var_t,4>({dl, (var_t) (lineral_watches[dl].size()-1), dl, dl_count[dl]}) );
        const auto [lt2,val] = l.get_assignment(alpha);
        //if lineral_watches.back() is already assigned, update alpha!
        //const auto [lt2,val] = lineral_watches[dl].back().get_assignment(alpha);
        if(val!=bool3::None) {
          assert( dl == l.get_assigning_lvl(alpha_dl) );
          trails[dl].emplace_back( lt2, trail_t::IMPLIED_ALPHA, rs );
          assert( alpha[lt2]==val || alpha[lt2]==bool3::None );
          alpha[lt2] = val;
          alpha_dl[lt2] = dl;
          assert(alpha_dl[lt2] == l.get_assigning_lvl(alpha_dl)); //TODO this should always be true!
          VERB(70, "c " + std::to_string(dl) + " : new ALPHA " + l.get_assigning_xlit(alpha).to_str() + " from UNIT " + lit.to_str() + (type!=trail_t::LINERAL_IMPLIED_ALPHA ? (rs<xclss.size() ? " with reason clause " + xclss[rs].to_str() : "") : (" with reason clause " + lineral_watches[0][rs].to_str()) ) );
          alpha_trail_pos[lt2] = (var_t) trails[dl].size()-1;
          if(rs<xclss.size() && type!=trail_t::LINERAL_IMPLIED_ALPHA) xclss[rs].set_assigning_lvl(dl);
      #ifdef EXACT_UNIT_TRACKING
          if(lt!=lt2) {
            //update assignments
            assert( assignments[lt2].is_zero() || assignments_dl[lt2] == alpha_dl[lt2] );
            //either lt2 has not been assigned yet; or it has been done on this level; i.e., we can just overwrite it! (note: here we have a forcing assignment, i.e., a better assignment...)
            //trails[ alpha_dl[lt2] ].emplace_back( lt2, trail_t::IMPLIED_ALPHA );
            assignments[lt2] = lineral_watches[dl].back().get_assigning_xlit(alpha);
            assignments_dl[lt2] = alpha_dl[lt2];
          }
      #endif
        } else if (l.is_equiv()) { //TODO update to check is_equiv for xlit_watches!!
      #ifdef USE_EQUIV
          assert(lt < l.get_equiv_lit() ); //ensure that lt is smallest!
          equiv_lits[lt].set_ind( l.get_equiv_lit() );
          equiv_lits[lt].set_polarity( l.has_constant() );
          equiv_lits[lt].set_reason( rs );
          equiv_lits_dl[lt] = lvl;
          assert( l.get_assigning_lvl(alpha_dl) == dl );
          trails[lvl].emplace_back( lt, trail_t::EQUIV, rs );
          VERB(65, "c " + std::to_string(lvl) + " : new EQUIV " + lineral_watches[lvl].back().to_str() )
          if(rs<xclss.size()) xclss[rs].set_assigning_lvl(lvl);
      #endif
        }

        return val!=bool3::None ? lt2 : -1;
      } else {
          //type now is either IMPLIED_ALPHA or LINERAL_IMPLIED_ALPHA or LEARNT_UNIT, i.e., we already knew that an alpha was implied!
          assert( _reduced_lit.is_assigning() );
          const var_t lt2 = _reduced_lit.LT();
          const bool3 val = to_bool3( _reduced_lit.has_constant() );

          trails[dl].emplace_back( lt2, type, rs );
          assert( alpha[lt2]==val || alpha[lt2]==bool3::None );
          alpha[lt2] = val;
          alpha_dl[lt2] = dl;
          assert(alpha_dl[lt2] == lineral_watches[dl].back().get_assigning_lvl(alpha_dl)); //TODO this should always be true!
          VERB(70, "c " + std::to_string(dl) + " : new ALPHA " + _reduced_lit.to_str() + " from UNIT " + lit.to_str() + ( type!=trail_t::LINERAL_IMPLIED_ALPHA && type!=trail_t::LEARNT_UNIT ? (rs<xclss.size() ? " with reason clause " + xclss[rs].to_str() : "") : (" with reason clause " + lineral_watches[0][rs].to_str()) ) );
          alpha_trail_pos[lt2] = (var_t) trails[dl].size()-1;
          if(type!=trail_t::LINERAL_IMPLIED_ALPHA && rs<xclss.size()) xclss[rs].set_assigning_lvl(dl);
          return lt2;
      }
    };

    /**
     * @brief queue implied lineral for propagation (one-by-one); update data using propagate_implied_lineral
     * 
     * @param lin lineral to be added to data structures
     * @param rs rs_cls_idx of reason clause
     * @param type type of propagation (defaults to trail_t::IMPLIED_UNIT)
     * @return always true
     */
    inline bool queue_implied_lineral(const xlit& lin, const var_t& rs, const trail_t type = trail_t::IMPLIED_UNIT, const var_t lvl = -1) {
      assert(type==trail_t::IMPLIED_UNIT || type==trail_t::GUESS || type==trail_t::LEARNT_UNIT);
      if(lin.LT()==0) lineral_queue.emplace_front( lin, rs, type, lvl );
      else lineral_queue.emplace_back( lin, rs, type, lvl );
      return true;
    }
    
    /**
     * @brief queue implied lineral for propagation (one-by-one); update data using propagate_implied_lineral
     * 
     * @param ind var-idx to be assigned
     * @param bool3 val value of alpha-assignment
     * @param rs rs_cls_idx of reason clause
     * @param type type of propagation (defaults to trail_t::NEW_ALPHA)
     * @return always true
     */
    inline bool queue_implied_alpha(const var_t& ind, const bool3& val, const var_t& rs, const trail_t type = trail_t::IMPLIED_ALPHA, const var_t lvl = -1) {
      assert(type==trail_t::IMPLIED_ALPHA || type==trail_t::LINERAL_IMPLIED_ALPHA);
      if(ind==0) lineral_queue.emplace_front( xlit(ind, b3_to_bool(val)), rs, type, lvl );
      else lineral_queue.emplace_back( xlit(ind, b3_to_bool(val)), rs, type, lvl );
      return true;
    }

    /**
     * @brief propagates lineral from queue until a new alpha is propagated or the queue is empty
     * 
     * @return var_t idx of new lt; or 0 if no new alpha was propagated; conflict can be checked with no_conflict() (!)
     */
    inline var_t propagate_implied_lineral() {
      if(lineral_queue.empty()) return false;
      var_t new_lt = -1;
      while( (new_lt == (var_t) -1) && !lineral_queue.empty() ) {
        const auto& [lin, type, rs, lvl] = lineral_queue.front();
        //TODO special handling if type is IMPLIED ALPHA or LINERAL IMPLIED ALPHA
        new_lt = add_implied_lineral(lin, rs, type, lvl);
        lineral_queue.pop_front();
      }
      return new_lt;
    }

    
    
    /**
     * @brief adds new lineral to data structure that holds already at dl 0; then propagates new information -- assumes that it becomes assigning at current dl!
     * 
     * @param lit linteral to be added
     * @return true iff xlit was actually new at current dl!
     */
    inline bool add_new_lineral(const xlit& lit) {
      //store lit in 
      _reduced_lit = lit;
      _reduced_lit.reduce(alpha, alpha_dl, 0); //reduce with alpha assignments at lvl 0
      if(!_reduced_lit.is_assigning()) {
        _reduced_lit.reduce(equiv_lits, equiv_lits_dl, 0); //reduce equivalent variables
      }
  #ifdef EXACT_UNIT_TRACKING
      if(!_reduced_lit.is_assigning()) {
        _reduced_lit.reduce(assignments, assignments_dl, dl); //reduce with assignments AND alpha...
      }
  #endif
      if(_reduced_lit.is_zero()) return false; 
      VERB(65, "c " + std::to_string(0) + " : new UNIT " + lit.to_str() + " ~> " + _reduced_lit.to_str() );

#ifdef EXACT_UNIT_TRACKING
      const var_t lt = _reduced_lit.LT();
      // update assignments
      assert(assignments[lt].is_zero() || _reduced_lit == assignments[lt]);
      if(assignments[lt].is_zero()) {
        assignments[lt] = _reduced_lit;
        assignments_dl[lt] = dl;
      }
      //add _reduced_lit to assignments_xsys
      assert((var_t)state_stack.size() >= 0);
      for(auto i = 1; i < (var_t) state_stack.size(); ++i) {
        state_stack[i].L += xsys(_reduced_lit);
      }
      assignments_xsys += xsys(_reduced_lit);
#endif
      //TODO what to do if lit becomes an equivilan e on some intermediate dl? schould we keep track of that?! (certainly if lin is has assigning_lvl l, then it is an equivalence at l-1 (!))

      trails[0].emplace_back( _reduced_lit.LT(), trail_t::IMPLIED_UNIT, -1);
      lineral_watches[0].emplace_back( std::move(_reduced_lit), alpha, alpha_dl, 0, dl_count, -1 );
      assert( lineral_watches[0].back().is_active(dl_count) );
      // add to L_watch_list's -- if there is anything to watch
      if(lineral_watches[0].back().size()>0) {
        L_watch_list[ lineral_watches[0].back().get_wl0() ].emplace_back( std::array<var_t,4>({0, (var_t) (lineral_watches[0].size()-1), 0, dl_count[0]}) );
        if(lineral_watches[0].back().get_wl0() != lineral_watches[0].back().get_wl1()) L_watch_list[ lineral_watches[0].back().get_wl1() ].emplace_back( std::array<var_t,4>({0, (var_t) (lineral_watches[0].size()-1), 0, dl_count[0]}) );
      }

#ifdef EXACT_UNIT_TRACKING
      if(lt!=lt2) {
        //update assignments
        assert( assignments[lt2].is_zero() || assignments_dl[lt2] == alpha_dl[lt2] );
        //either lt2 has not been assigned yet; or it has been done on this level; i.e., we can just overwrite it! (note: here we have a forcing assignment, i.e., a better assignment...)
        //trails[ alpha_dl[lt2] ].emplace_back( lt2, trail_t::IMPLIED_ALPHA );
        assignments[lt2] = lineral_watches[0].back().get_assigning_xlit(alpha);
        assignments_dl[lt2] = alpha_dl[lt2];
      }
#endif
      
      return true;
    };

    /**
     * @brief triangulates watched linerals; i.e. updates them w.r.t. previous linearls and brings them in non-reduced row-echelon form
     */
    inline xsys get_assignments_xsys() {
      vec<xlit> lits; lits.reserve(lineral_watches.size());
      for(const auto& l_dl : lineral_watches) {
          for(const auto& l : l_dl) if(l.is_active(dl_count)) lits.emplace_back( l.to_xlit() );
      }
      return xsys( std::move(lits) );

      //triangulate code snippet -- NOT WORKING!
//
//      //we need to rewrite the current history, i.e., trails, alpha, alpha_dl, assignments, assignments_dl, assignments_list, lineral_watches and L_watch_list -- as if we reduced every new unit directly with the previous units!
//      
//      //reduce all watched linerals, and update assignments_list AND L_watch_list
//      vec< vec< std::array<var_t,4> > > assignments_list_new;
//      assignments_list_new.resize(opt.num_vars+1);
//      vec<var_t> assignments_list_index(assignments_list.size(),0);
//
//      //empty watch-lists
//      L_watch_list.clear();
//      L_watch_list.resize(opt.num_vars+1);
//
//      for(var_t lvl = 0; lvl <= dl; ++lvl) {
//        for(const auto& [lt,__] : trails[lvl]) {
//          const auto& [_, i, dl_, dl_c] = assignments_list[lt][assignments_list_index[lt]];
//          ++assignments_list_index[lt];
//          assert( _ == lvl && dl_ == lvl );
//          if(dl_count[dl_] != dl_c) continue;
//
//          //reduce with previous assignments, then update L_watch_list
//          xlit& lit = lineral_watches[lvl][i];
//          //reduce
//          while( !assignments_list_new[lit.LT()].empty() ) {
//            const auto& [lvl2, i2, dl2, dl_c2] = assignments_list_new[lit.LT()].back();
//            assert( dl_count[dl2] == dl_c2 );
//            lit += lineral_watches[lvl2][i2];
//          }
//          if(lit.is_zero()) continue;
//          //re-initialize lit
//          lineral_watches[lvl][i].init(alpha, alpha_dl);
//          //add to L_watch_list and assignments_list_new
//          assignments_list_new[lit.LT()].emplace_back( std::array<var_t,4>({_, i, dl_, dl_c}) );
//          L_watch_list[ lineral_watches[lvl].back().get_wl0() ].emplace_back( std::array<var_t,4>({_, i, dl_, dl_c}) );
//          if(lineral_watches[lvl].back().get_wl0() != lineral_watches[lvl].back().get_wl1()) L_watch_list[ lineral_watches[lvl].back().get_wl1() ].emplace_back( std::array<var_t,4>({_, i, dl_, dl_c}) );
//        }
//      }
//      //replace assignments_list by assignments_list_new
//      assignments_list = std::move(assignments_list_new);
//
//      VERB(65, "c triangulate end" )
    }



    /**
     * @brief adds a new cls to the database at dl 0
     * 
     * @param cls to be added
     * @param redundant bool to indicate whether the cls is redundant
     * @return var_t idx of new cls in vec<xcls_watch> xclss
     */
    inline var_t init_and_add_xcls_watch(xcls&& cls, const bool& redundant) {
      assert( dl == 0 );
      xcls_watch cls_w( std::move(cls) );
      cls_w.init(alpha, alpha_dl, dl_count);
      return add_xcls_watch( std::move(cls_w), redundant );
    }

    /**
     * @brief adds a new cls to the database
     * 
     * @param cls to be added
     * @param redundant bool to indicate whether the cls is redundant
     * @return var_t idx of new cls in vec<xcls_watch> xclss
     */
    inline var_t add_xcls_watch(xcls_watch&& cls, const bool& redundant, const bool learnt_cls = false) {
      xclss.emplace_back( std::move(cls) );
      utility.emplace_back( 0 );
      const var_t i = xclss.size()-1;
      //set redundancy
      xclss[i].set_redundancy(redundant);
      assert(redundant == !xclss[i].is_irredundant());
      //update active_cls
      if(xclss[i].is_irredundant()) ++active_cls;
      //update cls
      const auto ret = learnt_cls ? xclss[i].init_unit(alpha, alpha_dl, alpha_trail_pos, dl_count, equiv_lits, equiv_lits_dl) : xclss[i].init(alpha, alpha_dl, dl_count);
      //copied from GCP
      xlit new_unit;
      switch (ret) {
      case xcls_upd_ret::SAT:
          assert(xclss[i].is_sat(dl_count));
          assert(xclss[i].is_inactive(dl_count));
        #ifdef EXACT_UNIT_TRACKING
          assert(xclss[i].to_xcls().reduced(alpha).reduced(assignments).is_zero()); //in particular it must be zero when reduced with assignments!
        #endif
          // IGNORE THIS CLAUSE FROM NOW ON
          decr_active_cls(i);
          break;
      case xcls_upd_ret::UNIT: //includes UNSAT case (i.e. get_unit() reduces with assignments to 1 !)
          assert(xclss[i].is_unit(dl_count));
          assert(xclss[i].is_inactive(dl_count));
        #ifdef EXACT_UNIT_TRACKING
          assert(xclss[i].to_xcls().reduced(alpha).reduced(assignments).is_unit() || xclss[i].to_xcls().reduced(alpha).reduced(assignments).is_zero());
        #endif
          //update utility
          utility[i]++;
          // IGNORE THIS CLAUSE FROM NOW ON
          decr_active_cls(i);
          // NEW LIN-EQS
          if( queue_implied_lineral(std::move(xclss[i].get_unit()), i) ) {
            #ifdef EXACT_UNIT_TRACKING
              assert(xclss[i].to_xcls().reduced(alpha).reduced(assignments).is_zero()); //in particular it must now be zero w.r.t. assignments (since new_unit has already been added!)
            #endif
          }
          if (!no_conflict()) { 
              VERB(70, "UNSAT with conflict clause " + get_last_reason().to_str()); 
              return i; //quit propagation immediately at conflict!
          }
          break;
      case xcls_upd_ret::NONE:
          assert(xclss[i].is_none(dl_count));
          assert(xclss[i].is_active(dl_count));
          break;
      }
      // add new cls to watch_lists
      watch_list[ (xclss.back().get_wl0()) ].emplace_back(i);
      watch_list[ (xclss.back().get_wl1()) ].emplace_back(i);
      assert(assert_data_structs());
      return i;
    }

    /**
     * @brief restarts the solver; i.e. rm all assignments and backtracks to dl 0
     */
    void restart(stats& s);

  public:
    /**
     * @brief Construct a new impl graph where each vector in clss represents a xor-clause; they must be of length at most two!
     * 
     * @param clss vector of xlit-vectors that represent the clauses
     * @param opt_ options for heuristics, also includes number of vars
     * @param ext bool decides whether extended graph is constructed
     */
    solver(const vec< vec<xlit> >& clss, const options& opt_, const var_t dl_ = 0) noexcept;

    /**
     * @brief Construct a new impl graph
     * 
     * @param parsed_xnf pair of options and clauses, as returned by parse_file
     * @param ext bool decides whether extended graph is constructed
     */
    solver(parsed_xnf& p_xnf) noexcept : solver(p_xnf.cls, options(p_xnf.num_vars, p_xnf.num_cls), 0) {};

    //copy ctor
  #ifdef EXACT_UNIT_TRACKING
    solver(const solver& o) noexcept : xclss(o.xclss), utility(o.utility), watch_list(o.watch_list), L_watch_list(o.L_watch_list), opt(o.opt), dl(o.dl), active_cls(o.active_cls), state_stack(o.state_stack), activity_score(o.activity_score), dl_count(o.dl_count), assignments(o.assignments), lineral_watches(o.lineral_watches), alpha(o.alpha), last_phase(o.last_phase), alpha_dl(o.alpha_dl), alpha_trail_pos(o.alpha_trail_pos), assignments_dl(o.assignments_dl), equiv_lits(o.equiv_lits), equiv_lits_dl(o.equiv_lits_dl), trails(o.trails), lineral_queue(o.lineral_queue) { assert(assert_data_structs()); };
  #else
    solver(const solver& o) noexcept : xclss(o.xclss), utility(o.utility), watch_list(o.watch_list), L_watch_list(o.L_watch_list), opt(o.opt), dl(o.dl), active_cls(o.active_cls), state_stack(o.state_stack), activity_score(o.activity_score), dl_count(o.dl_count), lineral_watches(o.lineral_watches), alpha(o.alpha), last_phase(o.last_phase), alpha_dl(o.alpha_dl), alpha_trail_pos(o.alpha_trail_pos), equiv_lits(o.equiv_lits), equiv_lits_dl(o.equiv_lits_dl), trails(o.trails), lineral_queue(o.lineral_queue) { assert(assert_data_structs()); };
  #endif

    ~solver() = default;
    
    void GCP(stats& s);
    
    /**
     * @brief saves current state to state_stack
     */
    void save_state();

    /**
     * @brief backtracks to dl
     */
    void backtrack(const var_t& lvl);


    //decision heuristics
    /*
     * @brief branch on first vertex (i.e. vert at first position in L)
     */
    std::pair< xsys, xsys > dh_vsids_UNFINISHED() const;

    /*
     * @brief branch on ind that has the shortest watch_list
     */
    std::pair< xsys, xsys > dh_shortest_wl() const;

    /*
     * @brief branch on ind that has the longest watch_list
     */
    std::pair< xsys, xsys > dh_longest_wl() const;

    /*
     * @brief branch on x[i] where i smallest ind not yet guessed!
     */
    std::pair< xsys, xsys > dh_lex_LT() const;

    //solve-main
    void solve(stats& s); //{ opt.ca = ca_alg::dpll; return cdcl_solve(s); };
    stats solve() { stats s; solve(s); return s; };
    
    void dpll_solve(stats& s);
    stats dpll_solve() { stats s; dpll_solve(s); return s; };

    var_t get_dl() const noexcept { return dl; };
    
    options* get_opts() { return &opt; };
    const options* get_const_opts() const { return &opt; };

    std::string to_str() const noexcept;
    std::string to_xnf_str() const noexcept;

    solver& operator=(const solver& ig) = delete;

    bool assert_data_structs() const noexcept;
    void print_assignments(std::string lead = "") const noexcept;
    void print_trail(std::string lead = "") const noexcept;

};