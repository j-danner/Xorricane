#pragma once

#include <stack>
#include <math.h>
#include <map>
#include <list>
#include <queue>
#include <memory>
#include <array>
#include <m4ri/m4ri.h>
#include <sstream>

#include "solve.hpp"
#include "misc.hpp"
#include "xlit/xlit.hpp"
#include "xlit/xlit_watch.hpp"
#include "xlit/xsys.hpp"
#include "xlit/xcls.hpp"
#include "xlit/xcls_watch.hpp"
#include "order_heap/heap.h"


#define TRAIL trails.back()

using xlit_w_it = std::list<xlit_watch>::iterator;

enum class trail_t { EQUIV, IMPLIED_UNIT, IMPLIED_ALPHA, GUESS };

struct trail_elem {
  /**
   * @brief indeterminate that is affected by this trail elem
   */
  var_t ind;
  /**
   * @brief type of trail elem
   */
  trail_t type;
  /**
   * @brief pointer to associated xlit_watch
   */
  xlit_w_it lin;

  trail_elem() : ind(0), type(trail_t::IMPLIED_UNIT) {};
  trail_elem(const var_t& _ind, const trail_t& _type, xlit_w_it _lin) : ind(_ind), type(_type), lin(_lin) {};
  trail_elem(const trail_elem& other) : ind(other.ind), type(other.type), lin(other.lin) {};
  trail_elem(trail_elem&& other) : ind(other.ind), type(other.type), lin(other.lin) {};
};

struct lineral_queue_elem {
  xlit_w_it lin;
  trail_t type;

  lineral_queue_elem() : lin(), type(trail_t::IMPLIED_ALPHA) {};
  lineral_queue_elem(xlit_w_it _lin, const trail_t& _type) : lin(_lin), type(_type) {};
  lineral_queue_elem(const lineral_queue_elem& other) : lin(other.lin), type(other.type) {};
  lineral_queue_elem(lineral_queue_elem&& other) : lin(other.lin), type(other.type) {}; 
};

struct watch_list_elem {
  var_t lvl;
  xlit_w_it lin;
  dl_c_t dl_c;
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
     * @brief L_watch_list[lt] stores elements of the form [lvl, i, dl_c]; indicating that lineral_watches[lvl][i] watches lt IFF dl_count[lvl]==dl_c
     */
    vec< std::list< watch_list_elem > > L_watch_list;


    /**
     * @brief options for heuristics of solver (and more)
     */
    options opt;

    /**
     * @brief current decision level
     */
    var_t dl = 0;

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
    vec< std::list< xlit_watch > > lineral_watches;

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
     * @todo refactor trails to be a SINGLE stack; and alpha_trail_pos indicates the postiion in this single stack; 
     *       would simplify code for determining the highest position in trail_stack + simplify filtration tracking?
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

    var_t get_num_vars() const { return alpha.size()-1; };
    
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
      const var_t i = add_xcls_watch( std::move(cls), redundant, true );
      utility[i]++;
      return i;
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

    /**
     * @brief pops last element in TRAIL; updates alpha and alpha_dl if 'IMLIED_ALPHA' is rm
     * 
     * @return true 
     * @return false 
     */
    inline void pop_trail() {
      assert(!TRAIL.empty());
      //add ind back to heap
      if(!order_heap_vsids.inHeap(TRAIL.back().ind)) order_heap_vsids.insert( TRAIL.back().ind );
      //fix lineral_watches, alpha, alpha_dl and alpha_trail_pos
      switch(TRAIL.back().type) {
      case trail_t::GUESS:
      case trail_t::IMPLIED_UNIT:
        assert(TRAIL.back().lin->LT() == TRAIL.back().ind);
        break;
      case trail_t::IMPLIED_ALPHA:
        //store last_phase
        save_phase();
        alpha[TRAIL.back().ind] = bool3::None;
        alpha_dl[TRAIL.back().ind] = (var_t) -1;
        alpha_trail_pos[TRAIL.back().ind] = (var_t) -1;
        break;
      case trail_t::EQUIV:
        assert(equiv_lits[TRAIL.back().ind].is_active());
        equiv_lits[TRAIL.back().ind].clear();
        equiv_lits_dl[TRAIL.back().ind] = (var_t) 0;
        assert(!equiv_lits[TRAIL.back().ind].is_active());
        break;
      }
      TRAIL.pop_back();
    }
    
    /**
     * @brief construct reason cls by resolving list of xclss; new clause is added to xclss
     * 
     * @param rs_cls_idxs list of linerals whose reasons to resolve
     * @param add_idx additional index to resolve with
     * @return var_t indedx position of new xcls_watch
     */
    inline xcls_watch get_reason(const std::list<xlit_w_it>& rs_cls_idxs, const var_t idx = (var_t) -1) const {
    #ifndef NDEBUG
      vec<xlit> lits; lits.reserve(lineral_watches.size());
      for(const auto& l_dl : lineral_watches) {
          for(const auto& l : l_dl) lits.emplace_back( l.to_xlit() );
      }
      xsys L_( std::move(lits) );

      xlit tmp;
    #endif
      //resolve cls to get true reason cls
      xcls_watch r_cls;

      for(const auto& lin : rs_cls_idxs) {
        const auto& r_cls2 = get_reason(lin);
      #ifndef NDEBUG
        tmp += r_cls2.get_unit();
      #endif
        if(r_cls.is_zero()) { //r_cls has not yet been instantiated
          r_cls = r_cls2;
          assert(r_cls.is_unit(dl_count));
        } else {
          //resolve cls
          assert(r_cls2.is_unit(dl_count));
          //extend r_cls2 with (unit of r_cls)+1, and r_cls with (unit of r_cls2)+1
          VERB(120, "c resolving clauses\nc   "+ BOLD(r_cls.to_str()) +"\nc and\nc   "+ BOLD(r_cls2.to_str()));
          r_cls.resolve(r_cls2, alpha, alpha_dl, alpha_trail_pos, dl_count);
          VERB(120, "c and get \nc   "+ BOLD(r_cls.to_str()));
        #ifndef NDEBUG
          VERB(120, "c tmp = "+tmp.to_str());
        #endif
          VERB(120, "c");
          assert( !L_.is_consistent() || L_.reduce(tmp+r_cls2.get_unit()).is_zero() );
          assert(r_cls.to_xcls().reduced(alpha).is_unit());
          assert( !L_.is_consistent() || L_.reduce( r_cls.to_xcls().reduced(alpha).get_unit()+tmp).is_constant() );
        }
      }
      //resolve with additional clause -- if required!
      if(idx != (var_t) -1) {
        const auto& r_cls2 = xclss[idx];
      #ifndef NDEBUG
        tmp += r_cls2.get_unit();
      #endif
        if(r_cls.is_zero()) { //r_cls has not yet been instantiated
          r_cls = r_cls2;
          assert(r_cls.is_unit(dl_count));
        } else {
          //resolve cls
          assert(r_cls2.is_unit(dl_count));
          //extend r_cls2 with (unit of r_cls)+1, and r_cls with (unit of r_cls2)+1
          VERB(120, "c resolving clauses\nc   "+ BOLD(r_cls.to_str()) +"\nc and\nc   "+ BOLD(r_cls2.to_str()));
          r_cls.resolve(r_cls2, alpha, alpha_dl, alpha_trail_pos, dl_count);
          VERB(120, "c and get \nc   "+ BOLD(r_cls.to_str()));
        #ifndef NDEBUG
          VERB(120, "c tmp = "+tmp.to_str());
        #endif
          VERB(120, "c");
          assert( !L_.is_consistent() || L_.reduce(tmp+r_cls2.get_unit()).is_zero() );
          assert(r_cls.to_xcls().reduced(alpha).is_unit());
          assert( !L_.is_consistent() || L_.reduce( r_cls.to_xcls().reduced(alpha).get_unit()+tmp).is_constant() );
        }
      }

      return r_cls;
      //place r_cls into xclss
      //xclss.emplace_back( std::move(r_cls) );
      //utility.emplace_back( 0 );
      //const var_t i = xclss.size()-1;
      ////set redundancy
      //xclss[i].set_redundancy(true);
      ////update active_cls
      ////update cls //TODO is init_unit rly needed here; shouldn't the clause already be initialized?
      //VERB(120, "c adding new clause: " + BOLD(xclss[i].to_str()) + "  --> gives with current assignments: "+xclss[i].to_xcls().reduced(alpha).to_str());
      //xclss[i].init_unit(alpha, alpha_dl, alpha_trail_pos, dl_count, equiv_lits, equiv_lits_dl);
      //return i;
    }

    inline const xcls_watch get_reason(xlit_w_it lin) const {
      //@todo rm dead code!
      VERB(120, "c constructing reason clause for "+lin->to_str());
      //const var_t idx = get_reason( lin->get_reason_idxs() );
      ////adapt reason_cls_idx of lin
      //lin->set_reason_idxs( idx );
      //return xclss[idx];
      const auto rs = get_reason( lin->get_reason_idxs(), lin->get_reason_idx() );

      assert( rs.is_unit(dl_count) && (rs.get_unit().reduced(alpha,equiv_lits)+lin->to_xlit().reduced(alpha,equiv_lits)).reduced(alpha,equiv_lits).is_zero() );
      return rs;
    }
    
    inline xcls_watch get_reason(const trail_elem& t) const {
      return get_reason(t.lin);
    }

    //@todo write get_reason_and_init(xlit_it lin)
    //      that computes the reason clause and stores it in database
    //      also changes lin->reason_idxs to point to this clause!

    typedef xlit (solver::*dec_heu_t)();
    typedef std::pair<var_t,xcls_watch> (solver::*ca_t)();

    void bump_score(const var_t& ind);
    void bump_score(const xsys& new_xsys);
    void bump_score(const xlit& lit);
    void decay_score();

    inline void add_new_guess(xlit&& l) {
      //update assignments
      lineral_watches[dl].emplace_back( std::move(l), alpha, alpha_dl, dl_count );
      queue_implied_lineral( std::prev(lineral_watches[dl].end()), trail_t::GUESS);
    };

    /**
     * @brief decrease active_cls by one -- starting at dl lvl
     * 
     * @param idx of xcls that became inactive
     */
    inline void decr_active_cls(const var_t& idx) {
      assert(!xclss[idx].is_active(dl_count));
      if(!xclss[idx].is_irredundant()) return;
      //update curr val
      assert(active_cls>0);
      --active_cls;
      //update vals in active_cls_stack
      for(var_t j = xclss[idx].get_inactive_lvl(dl_count)+1; j<active_cls_stack.size(); ++j) {
        assert(active_cls_stack[j]>0);
        --active_cls_stack[j];
      }
     #if !defined(NDEBUG) && defined(DEBUG_SLOW)
      //check if active_cls is updated to correct lvl!
      auto dl_count_cpy = dl_count;
      for(var_t lvl = dl; lvl>0; --lvl) {
          ++dl_count_cpy[lvl];
          xcls reduced = xclss[idx].to_xcls().reduced(alpha,alpha_dl,lvl-1);
          if(xclss[idx].get_inactive_lvl(dl_count)<lvl) {
            assert(!xclss[idx].is_active(dl_count_cpy));
            assert(reduced.is_unit() || reduced.is_zero());
          } else {
            assert(xclss[idx].is_active(dl_count_cpy));
            //NOTE: we do not know whether xclss[idx] is actually zero; it might
            //      happen that an unwatched lineral is reduced to zero already on a lower dl!
            //      Thus we cannot assume !reduced.is_unit() and !reduced.is_zero() (!)
          }
      }
     #endif
    }

    /**
     * @brief adds new xlit to data structure if deduced at current dl; also reduces with current assignments to find new true/false assignments
     * 
     * @param lin iterator to xlit_watch in lineral_queue
     * @param type tral_t of lineral specifying type of propagation
     * @todo write seperate funcs for types: IMPLIED_UNIT, IMPLIED_ALPHA and GUESS
     * 
     * @return var_t ind>=0 iff alpha[ind] is now assigned; ind==-1 means no new alpha-assignment
     */
    inline var_t add_implied_lineral(xlit_w_it lin, const trail_t type = trail_t::IMPLIED_UNIT) {
      if(type==trail_t::IMPLIED_UNIT) {
        VERB(65, "c " + std::to_string(dl) + " : new UNIT " + lin->to_str() + " ~> " + lin->to_str() + (type!=trail_t::GUESS ? (" with reason clause " + get_reason(lin).to_str()) : "") );
        lin->reduce(alpha, alpha_dl, dl_count);
        if(opt.eq) lin->reduce(alpha, alpha_dl, dl_count, equiv_lits);
      }
      if(lin->is_zero(alpha)) {
        if(lin->is_zero()) lineral_watches[dl].erase( lin );
        return -1;
      }
      
      //TODO should we always reduce?! consider the following:
      //we already have UNIT x1+x2+x3 and now get x1; as of now, we add x2+x3, even though x1 would be assigning!
      //DO NOT REDUCE WITH TOO LONG XORs otherwise it might blow up!
      // add to trail //TODO add in propoer position in trail!

      xlit_watch& l = *lin;
      if(type!=trail_t::IMPLIED_ALPHA) {
        //lin->update_lit(std::move(_reduced_lit), alpha, alpha_dl);
        trails[dl].emplace_back( l.LT(), type, lin); //TODO rm from trails?
        //if clause is active, i.e., not yet assigning add to watch lists; otherwise add assignment!
        if(l.is_active(alpha)) {
          // add to L_watch_list's -- if there is anything to watch
          if(l.size()>0) L_watch_list[ l.get_wl0() ].emplace_back( dl, lin, dl_count[dl] );
          if(l.size()>1) L_watch_list[ l.get_wl1() ].emplace_back( dl, lin, dl_count[dl] );
          //deal with new equivalence!
          if (l.is_equiv() && opt.eq) {
            const var_t lt = l.LT();
            assert(lt < l.get_equiv_lit() ); //ensure that lt is smallest!
            equiv_lits[lt].set_ind( l.get_equiv_lit() );
            equiv_lits[lt].set_polarity( l.has_constant() );
            equiv_lits[lt].set_lin( lin );
            equiv_lits_dl[lt] = dl;
            assert( l.get_equiv_lvl(alpha_dl) <= dl );
            trails[dl].emplace_back( lt, trail_t::EQUIV, lin );
            VERB(65, "c " + std::to_string(dl) + " : new EQUIV " + lin->to_str() )
            //if we are at dl 0, replace lt in all lineral_watches AND in all xclss with l.get_equiv_lit() (!)
            if(dl==0) remove_fixed_equiv(lt);
          }
          return -1;
        }
      }
      //now l must be an alpha-assignment!
      assert(l.is_assigning(alpha));
      //get alpha-assignment
      const auto [lt2,val] = l.get_assignment(alpha);
      assert(l.is_assigning(alpha) && val!=bool3::None);
      trails[dl].emplace_back( lt2, trail_t::IMPLIED_ALPHA, lin );
      assert( alpha[lt2]==val || alpha[lt2]==bool3::None );
      alpha[lt2] = val;
      alpha_dl[lt2] = dl;
      assert(lt2==0 || alpha_dl[lt2] == std::max(l.get_assigning_lvl(alpha_dl), dl));
      alpha_trail_pos[lt2] = (var_t) trails[dl].size()-1;
      VERB(70, "c " + std::to_string(dl) + " : new ALPHA " + l.get_assigning_xlit(alpha).to_str() + " from UNIT " + l.to_str() + (type!=trail_t::GUESS ? (" with reason clause " + get_reason(lin).to_str()) : "") );
      return lt2;
    };

    /**
     * @brief queue implied lineral for propagation (one-by-one); update data using propagate_implied_lineral
     * 
     * @param lin lineral to be added to data structures
     * @param rs rs_cls_idx of reason clause
     * @param type type of propagation (defaults to trail_t::IMPLIED_UNIT)
     */
    inline void queue_implied_lineral(xlit_w_it lin, const trail_t type = trail_t::IMPLIED_UNIT) {
      if(lin->LT()==0) lineral_queue.emplace_front( lin, type );
      else lineral_queue.emplace_back( lin, type );
    }
    
    /**
     * @brief queue implied lineral for propagation (one-by-one); update data using propagate_implied_lineral
     * 
     * @param ind var-idx to be assigned
     * @param bool3 val value of alpha-assignment
     * @param rs rs_cls_idx of reason clause
     * @param type type of propagation (defaults to trail_t::NEW_ALPHA)
     */
    inline void queue_implied_alpha(xlit_w_it lin) {
      const auto lt = lin->is_constant() ? 0 : lin->get_wl1();
      assert(alpha[lt] == bool3::None);

      if(lt==0) lineral_queue.emplace_front( lin, trail_t::IMPLIED_ALPHA );
      else lineral_queue.emplace_back( lin, trail_t::IMPLIED_ALPHA );
    }

    /**
     * @brief propagates lineral from queue until a new alpha is propagated or the queue is empty
     * 
     * @return var_t idx of new lt; or -1 if no new alpha was propagated
     */
    inline var_t propagate_implied_lineral() {
      assert(!lineral_queue.empty());
      auto& [lin, type] = lineral_queue.front();
      var_t new_lt = add_implied_lineral(lin, type);
      lineral_queue.pop_front();
      return new_lt;
    }

    
    
    /**
     * @brief adds new lineral to data structure that holds already at dl 0; then propagates new information -- assumes that it becomes assigning at current dl!
     * 
     * @param lit linteral to be added
     * @return true iff xlit was actually new at current dl!
     */
    inline bool add_new_lineral([[maybe_unused]] const xlit& lit) {
      assert(false);
      return true;
    };

    int ctr = 0;
    /**
     * @brief decides whether a linear algebra in-processing step should be performed
     */
    bool need_linalg_inprocessing() {
      if(!no_conflict()) return false;
      if(dl==0) return true; //always use linear algebra on dl 0?
      if(opt.lin_alg_schedule==0) return false;
      ++ctr;
      ctr %= opt.lin_alg_schedule;
      return ctr == 0 && no_conflict();
    }

    /**
     * @brief get all implied alpha's from lineral assignments
     * @note might backtrack if a propagation on a lower dl is noticed!
     * 
     * @return list of reason clauses for new alpha assignments
     */
    bool find_implications_from_linerals(stats& s) {
      ++s.no_linalg;
    #ifndef NDEBUG
      vec<xlit> lits; lits.reserve(lineral_watches.size());
      for(const auto& l_dl : lineral_watches) {
          for(const auto& l : l_dl) lits.emplace_back( l.to_xlit() );
      }
      xsys L_( std::move(lits) );
    #endif
      VERB(80, "c use M4RI to find implied alpha from linerals");
      std::list< std::list<var_t> > r_clss;

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

      //fill with xlits
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
     
      //read results
      std::list<xlit> xlits_;
      vec<var_t> idxs;
      for(rci_t r = rank-1; r>0; --r) {
        idxs.clear();
        for(rci_t c=0; (unsigned)c<n_vars; ++c) {
            if( mzd_read_bit(M, r, c) ) idxs.push_back(perm_inv[c]);
        }
        if(idxs.size()==0) {
          //we got 1, i.e., we have a conflict; all other alpha assignments can be ignored
          assert(xlits_.size()==0);
          assert(mzd_read_bit(M,r,n_vars));
          xlits_.emplace_back( 0, false );
          break;
        }
        if(idxs.size()==1 && alpha[idxs[0]]!=to_bool3(mzd_read_bit(M,r,n_vars)) ) {
          xlits_.emplace_back( idxs[0], (bool) mzd_read_bit(M, r, n_vars) );
        }
        if(idxs.size()==2 && equiv_lits[idxs[0]].ind==0 && opt.eq) {
          assert(idxs[0] < idxs[1]);
          xlits_.emplace_back( std::move(idxs), (bool) mzd_read_bit(M, r, n_vars), presorted::yes );
        }
      }
      mzd_free(M);
      VERB(80, "c reduction done.");
      // (2) if pure assignment is contained in sys, construct reason cls!
      if(xlits_.size()==0) {
        VERB(80, "c no new alpha-assignments found!")
        mzd_free(M_tr);
        return false;
      }

      mzd_t* B = mzd_init(std::max(ncols,nrows), xlits_.size());
      VERB(80, "c found "+std::to_string(xlits_.size())+" new alpha assignments and equivs");
      idx = 0;
      for(const auto& lit : xlits_) {
        VERB(85, "c   `--> " + lit.to_str());
        //set bits of b according to xlits_
        for(const auto& jdx : lit.get_idxs_()) mzd_write_bit(B, perm[jdx], idx, 1);
        mzd_write_bit(B, n_vars, idx, lit.has_constant()); //uses that supp[0]==0
        ++idx;
      }
      //solve for M^T x = B (i.e. xlits_)
    #ifndef NDEBUG
      const auto ret = mzd_solve_left(M_tr, B, 0, true);
      assert(ret == 0);
    #else
      mzd_solve_left(M_tr, B, 0, false); //skip check for inconsistency; a solution exists i.e. is found!
    #endif

      //construct corresponding reason clauses
      idx = 0;
      for(auto&& lit : xlits_) {
        VERB(95, "c constructing reason cls indices for "+lit.to_str());
        ++s.no_linalg_prop;
        
        std::list<xlit_w_it> r_cls_idxs;
        var_t resolving_lvl = 0;
      
      #ifndef NDEBUG
        xlit tmp;
      #ifdef DEBUG_SLOW
        r=0;
        for(var_t lvl=0; lvl<=dl; ++lvl) {
          const auto& l_dl = lineral_watches[lvl];
          //check solution:
          for(xlit_w_it l_it = l_dl.begin(); l_it != l_dl.end() && r < B->nrows; ++l_it, ++r) {
            const auto& l = *l_it;
            if(!mzd_read_bit(B,r,idx)) continue;
            tmp += l;
          }
        }
        assert(L_.reduce(tmp+lit).is_zero());
        tmp.clear();
      #endif
      #endif
        assert( L_.reduce(tmp+lit).is_zero() );
        
        r = 0;
        for(var_t lvl=0; lvl<=dl; ++lvl) {
          auto& l_dl = lineral_watches[lvl];
          if(l_dl.empty()) continue;
          VERB(95, "c processing linerals deduced on lvl "+std::to_string(lvl));
          for(xlit_w_it l_it = l_dl.begin(); l_it != l_dl.end() && r < B->nrows; ++l_it, ++r) {
            if(!mzd_read_bit(B,r,idx)) continue;
            const auto& l = *l_it;
          #ifndef NDEBUG
            tmp += l;
          #endif
            if(lvl>0 && r==0) {
              //NOTE here we assume that the first lineral on every dl>0 comes from a guess; i.e. skip it for resolution!
              continue;
            } 
            bump_score(l);
            resolving_lvl = lvl;
            r_cls_idxs.emplace_back( l_it );
            assert( L_.reduce(tmp+lit).is_zero() );
          }
        }
        assert((tmp+lit).reduced(alpha).is_zero());
        ++idx;
        //add lineral to lineral_watches
        const bool equiv = lit.is_equiv();
        lineral_watches[resolving_lvl].emplace_back( std::move(lit), alpha, alpha_dl, dl_count, std::move(r_cls_idxs) );
        //backtrack if necessary!
        if(resolving_lvl < dl) {
          backtrack(resolving_lvl);
          assert(resolving_lvl==dl);
          queue_implied_lineral( std::prev(lineral_watches[dl].end()), equiv ? trail_t::IMPLIED_UNIT : trail_t::IMPLIED_ALPHA);
          //return immediately
          break;
        }
        assert(resolving_lvl==dl);
        queue_implied_lineral( std::prev(lineral_watches[dl].end()), equiv ? trail_t::IMPLIED_UNIT : trail_t::IMPLIED_ALPHA);
      }

      mzd_free(B);
      mzd_free(M_tr);

      return true;
    }


    /**
     * @brief triangulates watched linerals; i.e. updates them w.r.t. previous linearls and brings them in non-reduced row-echelon form
     */
    inline std::tuple<xsys,xcls_watch> get_assignments_xsys() {
    #ifndef NDEBUG
      //simple implementation
      vec<xlit> lits; lits.reserve(lineral_watches.size());
      for(const auto& l_dl : lineral_watches) {
          for(const auto& l : l_dl) lits.emplace_back( l.to_xlit() );
      }
      xsys L_( std::move(lits) );
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

      //fill with xlits
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

      VERB(80, "c watched linerals are inconsistent!");

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
      std::list<xlit_w_it> r_cls_idxs;
      for(var_t lvl=0; lvl<=dl; ++lvl) {
        auto& l_dl = lineral_watches[lvl];
        VERB(85, "c processing linerals deduced on lvl "+std::to_string(lvl));
        for(auto l_it =l_dl.begin(); l_it!=l_dl.end(); ++l_it) {
          if(mzd_read_bit(b,r,0)) {
          #ifndef NDEBUG
            tmp += *l_it;
          #endif
            if(lvl>0 && r==0) {
              //NOTE here we assume that the first lineral on every dl>0 comes from a guess; i.e. skip it for resolution!
              ++r;
              continue;
            } 
            r_cls_idxs.emplace_back( l_it );
            assert( L_.reduce(tmp).is_zero() ); //reduces to 0 instead of 1, as 1 is in L_
          }
          ++r;
        }
      }
      assert(tmp.is_one());
      assert(!r_cls_idxs.empty());

      mzd_free(b);
      mzd_free(M_tr);

      return {L, get_reason(r_cls_idxs) };
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
      if(learnt_cls) VERB(90, "c XNF : " + xclss[i].to_xnf_str());
      const auto ret = learnt_cls ? xclss[i].init_unit(alpha, alpha_dl, alpha_trail_pos, dl_count) : xclss[i].init(alpha, alpha_dl, dl_count);
      //copied from GCP
      switch (ret) {
      case xcls_upd_ret::SAT:
          assert(!learnt_cls);
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
          lineral_watches[dl].emplace_back( std::move(xclss[i].get_unit()), alpha, alpha_dl, dl_count, i );
          queue_implied_lineral( std::prev(lineral_watches[dl].end()) );
          break;
      case xcls_upd_ret::NONE:
          assert(!learnt_cls); //must not happen for learnt clauses
          assert(xclss[i].is_none(dl_count));
          assert(xclss[i].is_active(dl_count));
          break;
      }
      // add new cls to watch_lists
      if(xclss.back().size()>0) watch_list[ (xclss.back().get_wl0()) ].emplace_back(i);
      if(xclss.back().size()>1) watch_list[ (xclss.back().get_wl1()) ].emplace_back(i);
      assert_slow(assert_data_structs());
      return i;
    }

    const unsigned int confl_until_restart_default = 1<<7; //number of conflicts between restarts
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
     * @param num_vars number of variables
     * @param opt_ options for heuristics, also includes number of vars
     */
    solver(const vec< vec<xlit> >& clss, const var_t num_vars, const options& opt_) noexcept;

    /**
     * @brief Construct main solver object from parsed_xnf
     * 
     * @param parsed_xnf pair of options and clauses, as returned by parse_file
     */
    solver(parsed_xnf& p_xnf) noexcept : solver(p_xnf.cls, p_xnf.num_vars, options()) {};
    
    /**
     * @brief Construct main solver object from parsed_xnf
     * 
     * @param parsed_xnf pair of options and clauses, as returned by parse_file
     */
    solver(parsed_xnf& p_xnf, options& opt_) noexcept : solver(p_xnf.cls, p_xnf.num_vars, opt_) {};
   
    /**
     * @brief Construct main solver object from parsed_xnf
     * 
     * @param parsed_xnf pair of options and clauses, as returned by parse_file
     * @param P guessing_path of vars
     */
    solver(parsed_xnf& p_xnf, guessing_path& P) noexcept : solver(p_xnf.cls, p_xnf.num_vars, options(P)) {};

    //copy ctor
    solver(const solver& o) noexcept : xclss(o.xclss), utility(o.utility), watch_list(o.watch_list), L_watch_list(o.L_watch_list), opt(o.opt), dl(o.dl), active_cls(o.active_cls), active_cls_stack(o.active_cls_stack), activity_score(o.activity_score), dl_count(o.dl_count), lineral_watches(o.lineral_watches), alpha(o.alpha), last_phase(o.last_phase), alpha_dl(o.alpha_dl), alpha_trail_pos(o.alpha_trail_pos), equiv_lits(o.equiv_lits), equiv_lits_dl(o.equiv_lits_dl), trails(o.trails), lineral_queue(o.lineral_queue) { assert(assert_data_structs()); };

    ~solver() = default;

    void remove_fixed_alpha(const var_t upd_lt);

    void remove_fixed_equiv(const var_t idx);
    
    void GCP(stats& s);

    /**
     * @brief performs linear algebra in-processing;
     * @note only call this on dl 0!
     * 
     * @param s stats
     * @return bool true iff new clauses were added, and new alpha assignments derived
     */
    bool initial_linalg_inprocessing(stats& s) {
      assert(dl==0);
      if( !need_linalg_inprocessing() ) return false;
      return find_implications_from_linerals(s);
    };

    /**
     * @brief backtracks to dl
     */
    void backtrack(const var_t& lvl);


    //decision heuristics
    /**
     * @brief branch on first vertex (i.e. vert at first position in L)
     */
    xlit dh_vsids();

    /**
     * @brief branch on ind that has the shortest watch_list
     */
    xlit dh_shortest_wl();

    /**
     * @brief branch on ind that has the longest watch_list
     */
    xlit dh_longest_wl();

    /**
     * @brief branch on x[i] where i smallest ind not yet guessed!
     */
    xlit dh_lex_LT();
    
    /**
     * @brief wrapper for dec_heu_t funcs to first guess according to guessing path
     * @note dh_gp<dh> also has type dec_heu_t
     */
    template<const dec_heu_t dh>
    xlit dh_gp();

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