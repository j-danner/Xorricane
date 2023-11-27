#pragma once

#include <stack>
#include <math.h>
#include <map>
#include <list>
#include <queue>
#include <memory>
#include <array>
#include <m4ri/m4ri.h>

#include "solve.hpp"
#include "misc.hpp"
#include "xlit/xlit.hpp"
#include "xlit/xlit_watch.hpp"
#include "xlit/xsys.hpp"
#include "xlit/xcls.hpp"
#include "xlit/xcls_watch.hpp"
#include "order_heap/heap.h"


#define TRAIL trails.back()


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

struct VarOrderLt { ///Order variables according to their activities
    const vec<double>&  activity_score;
    bool operator () (const var_t x, const var_t y) const {
      assert(x<activity_score.size() && y<activity_score.size());
      return activity_score[x] > activity_score[y];
    }

    explicit VarOrderLt(const vec<double>& _activity_score) : activity_score(_activity_score) {}
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
    vec<double> utility;
    double util_cutoff; //min utility to keep a clause on cleanup

    /**
     * @brief watch_list[i] contains all idxs j s.t. xclss[j] watches indet i
     */
    vec< std::list<var_t> > watch_list;
    
    /**
     * @brief TODO
     */
    vec< std::list< std::array<var_t,4> > > L_watch_list;

    /**
     * @brief options for heuristics of solver (and more)
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
    vec<var_t> active_cls_stack;
    
    /**
     * @brief 'activity' of each variable; used for decision heuristic
     * @note entries must be strictly positive! (otherwise max_path/max_tree might fail!)
     */
    vec<double> activity_score;
    double max_act_sc;
    double bump = 1;
    const float decay = 0.95;
    Heap<VarOrderLt> order_heap_vsids{ VarOrderLt(activity_score) };

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

    /**
     * @brief current unit watches
     * @note lineral_watches[lvl] contains all units added in dl lvl; used as stack
     */
    vec< vec< xlit_watch > > lineral_watches;
    //TODO change to vec< std::list< xlit_watch> > lineral_watches; (!)
    //should allow us to access contents more quickly!

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

    /**
     * @brief add new (learnt) clause to database
     * 
     * @param cls clause to be added; pointers must already be in correct shape (use init() and init_unit())
     * @param redundant bool to declare clause redundant or not; defaults to true
     * @return var_t idx of new clause; -1 if it was not added to clause database, i.e., cls was already a lineral
     */
    inline var_t add_learnt_cls(xcls_watch&& cls, const bool& redundant = true) {
        assert(lineral_queue.empty());
        if(cls.size()>=2) {
            const var_t i = add_xcls_watch( std::move(cls), redundant, true );
            assert(xclss[i].get_assigning_lvl() == dl); //ensure we did backtrack as far as possible!
            //assert(xclss[i].get_inactive_lvl(dl_count) == dl); //ensure we did backtrack as far as possible!
            utility[i]++;
            return i;
        } else {
            assert(cls.size()<=1);
            add_new_lineral( cls.get_unit() );
            queue_implied_lineral( cls.get_unit(), lineral_watches[0].size()-1, trail_t::LEARNT_UNIT );
            return -1;
        }
    }


    //saves the phase of the TRAIL in last_phase according to selected phase_option
    inline void save_phase() {
      switch (opt.po) {
      case phase_opt::rand:
        last_phase[TRAIL.back().ind] = rand()%2 ? bool3::True : bool3::False;
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
      //add ind back to heap
      if(!order_heap_vsids.inHeap(TRAIL.back().ind)) order_heap_vsids.insert( TRAIL.back().ind );
      //fix lineral_watches, alpha, alpha_dl and alpha_trail_pos
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
        //store last_phase
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


    typedef std::pair<xsys,xsys> (solver::*dec_heu_t)();
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
      assert(active_cls>0);
      --active_cls;
      //update vals in active_cls_stack
      for(var_t j = xclss[idx].get_inactive_lvl(dl_count)+1; j<active_cls_stack.size(); ++j) { assert(active_cls_stack[j]>0); --active_cls_stack[j]; }
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
      if(_reduced_lit.is_zero()) return -1; 
      VERB(65, "c " + std::to_string(lvl) + " : new UNIT " + lit.to_str() + " ~> " + _reduced_lit.to_str() + (type!=trail_t::LINERAL_IMPLIED_ALPHA && type!=trail_t::LEARNT_UNIT ? (rs<xclss.size() ? " with reason clause " + xclss[rs].to_str() : "") : (" with reason clause " + lineral_watches[0][rs].to_str()) ) );
      
      const var_t lt = _reduced_lit.LT();
      //TODO should we always reduce?! consider the following:
      //we already have UNIT x1+x2+x3 and now get x1; as of now, we add x2+x3, even though x1 would be assigning!
      //DO NOT REDUCE WITH TOO LONG XORs otherwise it might blow up!
      // add to trail //TODO add in propoer position in trail!

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
      if(_reduced_lit.is_zero()) return false; 
      VERB(65, "c " + std::to_string(0) + " : new UNIT " + lit.to_str() + " ~> " + _reduced_lit.to_str() );

      //TODO what to do if lit becomes an equivilance on some intermediate dl? schould we keep track of that?! (certainly if lin has assigning_lvl l, then it is an equivalence at l-1 (!))

      trails[0].emplace_back( _reduced_lit.LT(), trail_t::IMPLIED_UNIT, -1);
      lineral_watches[0].emplace_back( std::move(_reduced_lit), alpha, alpha_dl, 0, dl_count, -1 );
      assert( lineral_watches[0].back().is_active(dl_count) );
      // add to L_watch_list's -- if there is anything to watch
      if(lineral_watches[0].back().size()>0) {
        L_watch_list[ lineral_watches[0].back().get_wl0() ].emplace_back( std::array<var_t,4>({0, (var_t) (lineral_watches[0].size()-1), 0, dl_count[0]}) );
        if(lineral_watches[0].back().get_wl0() != lineral_watches[0].back().get_wl1()) L_watch_list[ lineral_watches[0].back().get_wl1() ].emplace_back( std::array<var_t,4>({0, (var_t) (lineral_watches[0].size()-1), 0, dl_count[0]}) );
      }

      return true;
    };


    /**
     * @brief get all implied alpha's from lineral assignments
     */
    inline void find_implied_alpha_from_linerals() {
    #ifndef NDEBUG
      //simple implementation
      vec<xlit> lits; lits.reserve(lineral_watches.size());
      for(const auto& l_dl : lineral_watches) {
          for(const auto& l : l_dl) if(l.is_active(dl_count)) lits.emplace_back( l.to_xlit() );
      }
      xsys L_( std::move(lits) );
      //return {L_,xcls_watch()};
    #endif
      //M4RI implementation
      VERB(80, "c use M4RI to find implied alpha from linerals");

      //(1) reduce watched linerals

      //construct matrix only with occuring lits
      vec<var_t> perm(alpha.size(), 0);
      vec<var_t> perm_inv(alpha.size(), 0);
      var_t n_wlins = 0;
      for(const auto& l_dl : lineral_watches) {
        for(const auto& l : l_dl) {
          if(!l.is_active(dl_count)) continue;
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

      //fill with xlits
      rci_t r = 0;
      for(const auto& l_dl : lineral_watches) {
        for(const auto& l : l_dl) {
          //std::cout << l.to_str() << std::endl;
          if(!l.is_active(dl_count)) continue;
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
      const rci_t rank = mzd_echelonize_pluq(M, true); //should we use mzd_echelonize instead?
      
      //mzd_print(M);
      //read results
      std::list<xlit> xlits_;
      vec<var_t> idxs;
      for(rci_t r = 0; r<rank; ++r) {
        idxs.clear();
        for(rci_t c=0; (unsigned)c<n_vars; ++c) {
            if( mzd_read_bit(M, r, c) ) idxs.push_back(perm_inv[c]);
        }
        if(idxs.size()==0 || (idxs.size()==1 && alpha[idxs[0]]!=to_bool3(mzd_read_bit(M,r,n_vars))) ) {
          xlits_.emplace_back( std::move(idxs), (bool) mzd_read_bit(M, r, n_vars), presorted::yes );
        }
      }
      VERB(80, "c reduction done.");
      // (2) if pure assignment is contained in sys, construct reason cls!
      if(xlits_.size()==0) {
        VERB(80, "c no new alpha-assignments found!")
        return;
      }

      VERB(80, "c found "+std::to_string(xlits_.size())+" new alpha assignments! resolving reason clauses...");
      for(const auto& lit : xlits_) {
        VERB(85, "c   `--> " + lit.to_str());
      }
      for(const auto& lit : xlits_) {
        if(alpha[lit.LT()] == to_bool3(lit.has_constant())) continue;
        VERB(80, "c constructing reason clause for "+lit.to_str());
        //solve for M^T x = lit
        //mzd_clear_bits(b, 0, 0, n_vars+1);
        mzd_t* b = mzd_init(std::max(ncols,nrows), 1);
        //set bits of b according to xlits_
        if(lit.size()>0) mzd_write_bit(b, perm[lit.LT()],0, 1);
        mzd_write_bit(b, n_vars, 0, lit.has_constant()); //uses that supp[0]==0
        mzd_t* M_tr_cpy = mzd_copy(NULL, M_tr);

        //find solution
        //mzd_print(M);
        //std::cout << std::endl;
        //mzd_print(M_tr_cpy);
        //std::cout << std::endl;
        //mzd_print(b);
        //std::cout << std::endl;
      #ifndef NDEBUG
        const auto ret = mzd_solve_left(M_tr_cpy, b, 0, true);
        assert(ret == 0);
      #else
        mzd_solve_left(M_tr_cpy, b, 0, false); //skip check for inconsistency; a solution exists i.e. is found!
      #endif
        //mzd_print(b);
        mzd_free(M_tr_cpy);
        
        for(var_t lvl=0; lvl<=dl; ++lvl) {
          const auto& l_dl = lineral_watches[lvl];
          for(var_t idx= 0; idx<l_dl.size(); ++idx) {
            VERB(80, std::to_string(lvl) + ": " + l_dl[idx].to_str());
          }
        }
        
      #ifndef NDEBUG
        xlit tmp;
      #endif
        r = 0;
        //resolve cls to get true reason cls
        xcls_watch r_cls;
        for(var_t lvl=0; lvl<=dl; ++lvl) {
          const auto& l_dl = lineral_watches[lvl];
          VERB(90, "c processing linerals deduced on lvl "+std::to_string(lvl));
          for(var_t idx= 0; idx<l_dl.size(); ++idx) {
            const auto& l = l_dl[idx];
            if(mzd_read_bit(b,r,0)) {
            #ifndef NDEBUG
              tmp += l;
            #endif
              if(lvl>0 && idx==0) {
                //NOTE here we assume that the first lineral on every dl>0 comes from a guess; i.e. skip it for resolution!
                r++;
                continue;
              } 
              if(r_cls.size()==0) { //r_cls has not yet been instantiated
                r_cls = l.get_reason()<xclss.size() ? xclss[l.get_reason()] : xcls_watch( std::move(xcls( std::move(l.plus_one()) )) );
              } else {
                bump_score(l);
                //resolve cls
                if( l.get_reason() < xclss.size() ) {
                  const auto& r_cls2 = xclss[l.get_reason()];
                  //add (unit of r_cls)+1 to r_cls2, and (unit of r_cls2)+1 to r_cls
                  VERB(90, "c resolving clauses\nc   "+ BOLD(r_cls.to_str()) +"\nc and\nc   "+ BOLD(r_cls2.to_str()));
                  r_cls.resolve(r_cls2, alpha, alpha_dl, alpha_trail_pos, dl_count, equiv_lits, equiv_lits_dl);
                  VERB(90, "c and get \nc   "+ BOLD(r_cls.to_str()));
                #ifndef NDEBUG
                  VERB(90, "c tmp = "+tmp.to_str());
                #endif
                  VERB(90, "c");
                } else {
                  assert(lvl == 0); //the reason cls should only be a unit clause if it was deduced at lvl 0 (!)
                  VERB(90, "c resolving clauses\nc   "+ BOLD(r_cls.to_str()) +"\nc and\nc   "+ BOLD(l.to_str()));
                  r_cls.add_to_unit( l, alpha, alpha_dl, alpha_trail_pos, dl_count, equiv_lits, equiv_lits_dl );
                  VERB(90, "c and get \nc   "+ BOLD(r_cls.to_str()));
                #ifndef NDEBUG
                  VERB(90, "c tmp = "+tmp.to_str());
                #endif
                  VERB(90, "c");
                }
              }
              assert( L_.reduce(tmp+lit).is_zero() );
            }
            //TODO can we do a cheap early abort?
            if( r_cls.get_assigning_lvl() < lvl && r_cls.get_unit().reduced(alpha) == lit) {
              assert( r_cls.get_unit().reduced(alpha) == lit );
              goto finalize;
            }
            ++r;
          }
        }
      finalize:
        assert((tmp+lit).reduced(alpha).is_constant());
        VERB(80, "c done, reason clause is "+r_cls.to_str()+" for assignment "+lit.to_str());
        mzd_free(b);
      }

      mzd_free(M_tr);
      mzd_free(M);
    }


    /**
     * @brief triangulates watched linerals; i.e. updates them w.r.t. previous linearls and brings them in non-reduced row-echelon form
     */
    inline std::tuple<xsys,xcls_watch> get_assignments_xsys() {
    #ifndef NDEBUG
      //simple implementation
      vec<xlit> lits; lits.reserve(lineral_watches.size());
      for(const auto& l_dl : lineral_watches) {
          for(const auto& l : l_dl) if(l.is_active(dl_count)) lits.emplace_back( l.to_xlit() );
      }
      xsys L_( std::move(lits) );
      //return {L_,xcls_watch()};
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
          if(!l.is_active(dl_count)) continue;
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

      //fill with xlits
      rci_t r = 0;
      for(const auto& l_dl : lineral_watches) {
        for(const auto& l : l_dl) {
          //std::cout << l.to_str() << std::endl;
          if(!l.is_active(dl_count)) continue;
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
      const rci_t rank = mzd_echelonize_pluq(M, true); //should we use mzd_echelonize instead?
      
      //mzd_print(M);
      //read results
      std::list<xlit> xlits_;
      vec<var_t> idxs;
      for(rci_t r = 0; r<rank; ++r) {
        idxs.clear();
        for(rci_t c=0; (unsigned)c<n_vars; ++c) {
            if( mzd_read_bit(M, r, c) ) idxs.push_back(perm_inv[c]);
        }
        xlits_.emplace_back( std::move(idxs), (bool) mzd_read_bit(M, r, n_vars), presorted::no );
      }

      xsys L = xsys( std::move(xlits_) );
      VERB(80, "c reduction done.");

      if(L.is_consistent()) {
        mzd_free(M);
        mzd_free(M_tr);
        return {L,xcls_watch()};
      }

      // (2) if 1 is contained in sys, construct reason cls!
      assert(!L_.is_consistent());

      VERB(80, "c watched linerals are inconsistent! resolving reason clause...");

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
      
    #ifndef NDEBUG
      xlit tmp;
    #endif
      r = 0;
      //resolve cls to get true reason cls
      xcls_watch r_cls;
      for(var_t lvl=0; lvl<=dl; ++lvl) {
        const auto& l_dl = lineral_watches[lvl];
        VERB(85, "c processing linerals deduced on lvl "+std::to_string(lvl));
        for(var_t idx= 0; idx<l_dl.size(); ++idx) {
          const auto& l = l_dl[idx];
          if(mzd_read_bit(b,r,0)) {
          #ifndef NDEBUG
            tmp += l;
          #endif
            if(lvl>0 && idx==0) {
              //NOTE here we assume that the first lineral on every dl>0 comes from a guess; i.e. skip it for resolution!
              r++;
              continue;
            } 
            if(r_cls.size()==0) { //r_cls has not yet been instantiated
              r_cls = l.get_reason()<xclss.size() ? xclss[l.get_reason()] : xcls_watch( std::move(xcls( std::move(l.plus_one()) )) );
            } else {
              bump_score(l);
              //resolve cls
              if( l.get_reason() < xclss.size() ) {
                const auto& r_cls2 = xclss[l.get_reason()];
                //add (unit of r_cls)+1 to r_cls2, and (unit of r_cls2)+1 to r_cls
                VERB(85, "c resolving clauses\nc   "+ BOLD(r_cls.to_str()) +"\nc and\nc   "+ BOLD(r_cls2.to_str()));
                r_cls.resolve(r_cls2, alpha, alpha_dl, alpha_trail_pos, dl_count, equiv_lits, equiv_lits_dl);
                VERB(85, "c and get \nc   "+ BOLD(r_cls.to_str()));
              #ifndef NDEBUG
                VERB(85, "c tmp = "+tmp.to_str());
              #endif
                VERB(85, "c");
              } else {
                assert(lvl == 0); //the reason cls should only be a unit clause if it was deduced at lvl 0 (!)
                VERB(85, "c resolving clauses\nc   "+ BOLD(r_cls.to_str()) +"\nc and\nc   "+ BOLD(l.to_str()));
                r_cls.add_to_unit( l, alpha, alpha_dl, alpha_trail_pos, dl_count, equiv_lits, equiv_lits_dl );
                VERB(85, "c and get \nc   "+ BOLD(r_cls.to_str()));
              #ifndef NDEBUG
                VERB(85, "c tmp = "+tmp.to_str());
              #endif
                VERB(85, "c");
              }
            }
            assert( tmp.is_one() || r_cls.to_xcls().get_ass_VS().reduce( tmp ).reduced(alpha, alpha_dl, 0).is_one() );
          }
          if( r_cls.get_assigning_lvl() < lvl ) {
            //early abort if r_cls is already assigning, i.e., already gives a conflict!
            assert( r_cls.get_unit().reduced(alpha).is_one() );
            goto finalize;
          }
          ++r;
        }
      }
      assert(tmp.is_one());

    finalize:
      mzd_free(b);
      mzd_free(M_tr);
      mzd_free(M);

      VERB(80, "c done, reason clause is "+r_cls.to_str());

      return {L,r_cls};
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
      if(xclss[i].is_irredundant()) {
        for(auto& a_cls : active_cls_stack) ++a_cls;
        ++active_cls;
      }
      //update cls //TODO is init_unit rly needed here; shouldn't the clause already be initialized?
      VERB(90, "c adding new clause: " + BOLD(xclss[i].to_str()) + "  --> gives with current assignments: "+xclss[i].to_xcls().reduced(alpha).to_str());
      const auto ret = learnt_cls ? xclss[i].init_unit(alpha, alpha_dl, alpha_trail_pos, dl_count, equiv_lits, equiv_lits_dl) : xclss[i].init(alpha, alpha_dl, dl_count);
      //copied from GCP
      xlit new_unit;
      switch (ret) {
      case xcls_upd_ret::SAT:
          assert(xclss[i].is_sat(dl_count));
          assert(xclss[i].is_inactive(dl_count));
          // IGNORE THIS CLAUSE FROM NOW ON
          decr_active_cls(i);
          break;
      case xcls_upd_ret::UNIT: //includes UNSAT case (i.e. get_unit() reduces with assignments to 1 !)
          assert(xclss[i].is_unit(dl_count));
          assert(xclss[i].is_inactive(dl_count));
          //update utility
          utility[i]++;
          // IGNORE THIS CLAUSE FROM NOW ON
          decr_active_cls(i);
          // NEW LIN-EQS
          queue_implied_lineral(std::move(xclss[i].get_unit()), i);
          if (!no_conflict()) { 
              VERB(70, "UNSAT with conflict clause " + get_last_reason().to_str()); 
              return i; //quit propagation immediately at conflict!
          }
          break;
      case xcls_upd_ret::NONE:
          assert(!learnt_cls); //must not happen for learnt clauses
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

    const unsigned int confl_until_restart_default = 1<<14; //number of conflicts between restarts
    unsigned int confl_until_restart = 0; //number of conflicts between restarts
    /**
     * @brief checks if a restart is needed
     * @return true iff we should restart now
     */
    bool need_restart() const;

    unsigned int confl_this_restart = 0; //number of conflicts since last restart
    /**
     * @brief restarts the solver; i.e. rm all assignments and backtracks to dl 0
     */
    void restart(stats& s);

    /**
     * @brief update params confl_unitl_restart according to restart heuristic; should be called after every call to restart()
     */
    void update_restart_schedule(const unsigned int& no_restarts);
    
  public:
    /**
     * @brief Construct main solver object
     * 
     * @param clss vector of xlit-vectors that represent the clauses
     * @param opt_ options for heuristics, also includes number of vars
     */
    solver(const vec< vec<xlit> >& clss, const options& opt_, const var_t dl_ = 0) noexcept;

    /**
     * @brief Construct main solver object from parsed_xnf
     * 
     * @param parsed_xnf pair of options and clauses, as returned by parse_file
     */
    solver(parsed_xnf& p_xnf) noexcept : solver(p_xnf.cls, options(p_xnf.num_vars, p_xnf.num_cls), 0) {};
   
    /**
     * @brief Construct main solver object from parsed_xnf
     * 
     * @param parsed_xnf pair of options and clauses, as returned by parse_file
     * @param P reordering of vars
     */
    solver(parsed_xnf& p_xnf, reordering& P) noexcept : solver(p_xnf.cls, options(p_xnf.num_vars, p_xnf.num_cls, P), 0) {};

    //copy ctor
    solver(const solver& o) noexcept : xclss(o.xclss), utility(o.utility), watch_list(o.watch_list), L_watch_list(o.L_watch_list), opt(o.opt), dl(o.dl), active_cls(o.active_cls), active_cls_stack(o.active_cls_stack), activity_score(o.activity_score), dl_count(o.dl_count), lineral_watches(o.lineral_watches), alpha(o.alpha), last_phase(o.last_phase), alpha_dl(o.alpha_dl), alpha_trail_pos(o.alpha_trail_pos), equiv_lits(o.equiv_lits), equiv_lits_dl(o.equiv_lits_dl), trails(o.trails), lineral_queue(o.lineral_queue) { assert(assert_data_structs()); };

    ~solver() = default;
    
    void GCP(stats& s);

    /**
     * @brief backtracks to dl
     */
    void backtrack(const var_t& lvl);


    //decision heuristics
    /*
     * @brief branch on first vertex (i.e. vert at first position in L)
     */
    std::pair< xsys, xsys > dh_vsids();

    /*
     * @brief branch on ind that has the shortest watch_list
     */
    std::pair< xsys, xsys > dh_shortest_wl();

    /*
     * @brief branch on ind that has the longest watch_list
     */
    std::pair< xsys, xsys > dh_longest_wl();

    /*
     * @brief branch on x[i] where i smallest ind not yet guessed!
     */
    std::pair< xsys, xsys > dh_lex_LT();

    //solve-main
    void solve(stats& s); //{ opt.ca = ca_alg::dpll; return cdcl_solve(s); };
    stats solve() { stats s; solve(s); return s; };
    
    void dpll_solve(stats& s);
    stats dpll_solve() { stats s; dpll_solve(s); return s; };

    //find all solutions of xsys
    void solve_L(const xsys& L, stats& s) const;

    var_t get_dl() const noexcept { return dl; };
    
    options* get_opts() { return &opt; };
    const options* get_const_opts() const { return &opt; };

    std::string to_str() const noexcept;
    std::string to_xnf_str() const noexcept;

    solver& operator=(const solver& ig) = delete;

    bool assert_data_structs() const noexcept;
    void print_assignments([[maybe_unused]] const std::string lead = "") const noexcept { return; };
    void print_trail(std::string lead = "") const noexcept;

};