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

#include "misc.hpp"
#include "io.hpp"
#include "xlit/xlit.hpp"
#include "xlit/xlit_watch.hpp"
#include "xlit/xsys.hpp"
#include "xlit/xcls.hpp"
#include "xlit/xcls_watch.hpp"
#include "xlit/xcls_watch_resolver.hpp"
#include "order_heap/heap.h"


#define TRAIL trails.back()

using xlit_w_it = list<xlit_watch>::iterator;

enum class trail_t { GUESS, ALPHA, EQUIV, UNIT };

enum class queue_t { NEW_GUESS, IMPLIED_ALPHA, NEW_EQUIV, NEW_UNIT };

std::ostream& operator<<(std::ostream& os, const trail_t& t);

std::ostream& operator<<(std::ostream& os, const queue_t& t);

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

  trail_elem() : ind(0) {};
  trail_elem(const var_t& _ind, const trail_t& _type, xlit_w_it _lin) : ind(_ind), type(_type), lin(_lin) {};
  trail_elem(const trail_elem& other) : ind(other.ind), type(other.type), lin(other.lin) {};
  trail_elem(trail_elem&& other) : ind(other.ind), type(other.type), lin(other.lin) {};

  constexpr trail_elem& operator=(const trail_elem& o) = default;
  
  void swap(trail_elem& o) noexcept {
    std::swap(ind, o.ind);
    std::swap(type, o.type);
    std::swap(lin, o.lin);
  };
};

struct lineral_queue_elem {
  /**
   * @brief lineral to 'propagate'/'add'
   */
  xlit_w_it lin;
  /**
   * @brief decision-level on which to propagate
   */
  var_t lvl;
  /**
   * @brief type of propagation: 'NEW_UNIT': reduce newly learnt unit + watch; 'NEW_GUESS': add new guess + watch; 'IMPLIED_UNIT': update alpha/alpha_dl data structures; 'NEW_EQUIV': reduce, update equiv_lits + watch;
   */
  queue_t type;

  lineral_queue_elem() : lin(), lvl((var_t) -1), type(queue_t::NEW_UNIT) {};
  lineral_queue_elem(xlit_w_it _lin, const var_t _lvl, const queue_t& _type) : lin(_lin), lvl(_lvl), type(_type) {};
  lineral_queue_elem(const lineral_queue_elem& other) = default;
  lineral_queue_elem(lineral_queue_elem&& other) = default;
};

//wrapper class that concats four queues
template<class T>
class lin_queue {
  //lin_queue structure: IMPLIED_ALPHA |  NEW_EQUIV  | NEW_UNIT
  public:
    list<T> q_confl;
    list<T> q_alpha;
    list<T> q_equiv;
    list<T> q_unit;

    lin_queue() noexcept {};

    size_t size() const { return q_confl.size()+q_alpha.size()+q_equiv.size()+q_unit.size(); };
    bool empty() const { return q_confl.empty() && q_alpha.empty() && q_equiv.empty() && q_unit.empty(); };

    deque<T>::reference front() {
      assert(!empty());
      if(!q_confl.empty())      return q_confl.front();
      else if(!q_alpha.empty()) return q_alpha.front();
      else if(!q_equiv.empty()) return q_equiv.front();
      else                      return q_unit.front();
    };

    void pop_front() {
      assert(!empty());
      if(!q_confl.empty())      q_confl.pop_front();
      else if(!q_alpha.empty()) q_alpha.pop_front();
      else if(!q_equiv.empty()) q_equiv.pop_front();
      else                      q_unit.pop_front();
    };
    
    /**
     * @brief clear all els in queue with too high level
     * 
     * @param lvl max lvl that is allowed in queue
     */
    void clear(const var_t lvl) {
      q_confl.remove_if([lvl](const auto& q_el){ return q_el.lvl > lvl; });
      q_alpha.remove_if([lvl](const auto& q_el){ return q_el.lvl > lvl; });
      q_equiv.remove_if([lvl](const auto& q_el){ return q_el.lvl > lvl; });
      q_unit.remove_if( [lvl](const auto& q_el){ return q_el.lvl > lvl; });
    }

    void clear() {
      q_confl.clear();
      q_alpha.clear();
      q_equiv.clear();
      q_unit.clear();
    }
};

struct watch_list_elem {
  var_t lvl;
  dl_c_t dl_c;
  xlit_w_it lin;
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
  friend xcls_watch_resolver;
  private:
    /**
     * @brief xor-clause watchers
     */
    vec< xcls_watch > xclss;

    /**
     * @brief utility[i] gives number of unit propagations of xclss[i] (with moving average) @todo fix this line!!
     */
    vec<double> utility;
    double util_cutoff; //min utility to keep a clause on cleanup

    /**
     * @brief watch_list[i] contains all idxs j s.t. xclss[j] watches indet i
     */
    vec< list<var_t> > watch_list;
    
    /**
     * @brief L_watch_list[lt] stores elements of the form [lvl, dl_c, lin]; indicating that lt is watched in *lin IFF dl_count[lvl]==dl_c
     */
    vec< list< watch_list_elem > > L_watch_list;


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
    inline bool at_conflict() const { return alpha[0]==bool3::True; };

    /**
     * @brief counts how often a dl was visited -- required to quickly discard xlit that were already watched previously in the current search tree
     *        dl_count[i] is the number of times the solver was at dl i (counting once after increasing dl and before decreasing dl)
     */
    vec<dl_c_t> dl_count;

    /**
     * @brief current unit watches
     * @note lineral_watches[lvl] contains all units added in dl lvl; used as stack
     */
    vec< list< xlit_watch > > lineral_watches;

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
     * @brief alpha_trail_pos[i] indicates the position of the alpha-assignment in trails[alpha_dl[i]], this value is unique!
     * @note if i and j are assigned: alpha_trail_pos[i] > alpha_trails_pos[j]  -->  alpha_dl[i] >= alpha_dl[j];
     */
    vec<var_t> alpha_trail_pos;

    /**
     * @brief if equiv_lits[i].ind is non-zero, i is congruent to equiv_lits[i].ind + (equiv_lits[i].polarity ? 1 : 0).
     * @note we must have i < equiv_lits[i].first
     */
    vec<equivalence> equiv_lits;

    /**
     * @brief trail of decisions/unit-propagations
     * @note trail[lvl] is the trail at level lvl
     */
    vec< list<trail_elem> > trails;

    /**
     * @brief total trail length up to dl-1
     */
    var_t stepwise_lit_trail_length = 1;

    lin_queue<lineral_queue_elem> lineral_queue;

    var_t get_num_vars() const { return alpha.size()-1; };
    
    std::pair<var_t,xcls_watch> analyze(solver& s);
    std::pair<var_t,xcls_watch> analyze_exp(solver& s);
    std::pair<var_t,xcls_watch> analyze_dpll();
    inline std::pair<var_t,xcls_watch> analyze_dpll([[maybe_unused]] solver& s) { return analyze_dpll(); };
    
    void minimize(xcls_watch& cls) const;

    /**
     * @brief add new (learnt) clause to database
     * 
     * @param cls clause to be added; pointers must already be in correct shape (use init() and init_unit())
     * @param redundant bool to declare clause redundant or not; defaults to true
     * @return var_t idx of new clause; -1 if it was not added to clause database, i.e., cls was already a lineral
     */
    inline var_t add_learnt_cls(xcls_watch&& cls, const bool& redundant = true) {
      const var_t i = add_xcls_watch( std::move(cls), redundant, true );
      ++utility[i];
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
      case trail_t::UNIT:
        assert(TRAIL.back().lin->LT() == TRAIL.back().ind);
        break;
      case trail_t::ALPHA:
        //store last_phase
        save_phase();
        alpha[TRAIL.back().ind] = bool3::None;
        alpha_dl[TRAIL.back().ind] = (var_t) -1;
        alpha_trail_pos[TRAIL.back().ind] = (var_t) -1;
        --stepwise_lit_trail_length;
        break;
      case trail_t::EQUIV:
        assert(equiv_lits[TRAIL.back().ind].is_active());
        equiv_lits[ equiv_lits[TRAIL.back().ind].ind ].set_prev_ind(0);
        equiv_lits[TRAIL.back().ind].clear();
        assert(!equiv_lits[TRAIL.back().ind].is_active());
        break;
      }
      TRAIL.back().lin->set_reducibility(true);
      TRAIL.pop_back();
    }
    
    /**
     * @brief construct reason cls by resolving list of xclss; new clause is added to xclss
     * 
     * @param rs_cls_idxs list of linerals whose reasons to resolve
     * @param add_idx additional index to resolve with
     * @param max_size maximal size in each filtration level, (var_t) -1 for default heuristic
     * @return var_t indedx position of new xcls_watch
     */
    inline xcls_watch get_reason_and_init(const list<xlit_w_it>& rs_cls_idxs, const var_t idx = (var_t) -1, const var_t max_size = (var_t) -1) {
    #ifndef NDEBUG
      vec<xlit> lits; lits.reserve(lineral_watches.size());
      for(const auto& l_dl : lineral_watches) {
          for(const auto& l : l_dl) lits.emplace_back( l.to_xlit() );
      }
      xsys L_( std::move(lits) );

      xlit tmp;
    #endif
      //resolve cls to get true reason cls
      xcls_watch_resolver r_cls;

      for(const auto& lin : rs_cls_idxs) {
        if(r_cls.is_zero()) { //r_cls has not yet been instantiated
          r_cls = get_reason_and_init(lin);
          assert(r_cls.is_unit(dl_count));
        #ifndef NDEBUG
          tmp += r_cls.get_unit();
        #endif
        } else {
          const auto& r_cls2 = get_reason_and_init(lin);
        #ifndef NDEBUG
          tmp += r_cls2.get_unit();
        #endif
          //resolve cls
          assert(r_cls2.is_unit(dl_count));
          //extend r_cls2 with (unit of r_cls)+1, and r_cls with (unit of r_cls2)+1
          VERB(120, "c resolving clauses\nc   "<< BOLD(r_cls.to_str()) <<"\nc and\nc   "<< BOLD(r_cls2.to_str()));
          r_cls.resolve(r_cls2, alpha, alpha_dl, alpha_trail_pos, dl_count);
          VERB(120, "c and get \nc   "<< BOLD(r_cls.to_str()));
        #ifndef NDEBUG
          VERB(120, "c tmp = "<<tmp.to_str());
        #endif
          VERB(120, "c");
          assert( !L_.is_consistent() || L_.reduce(tmp+r_cls2.get_unit()).is_zero() );
          assert(r_cls.to_xcls().reduced(alpha).is_unit());
          assert( !L_.is_consistent() || L_.reduce( r_cls.to_xcls().reduced(alpha).get_unit()+tmp).is_constant() );
        }
      }
      //resolve with additional clause -- if required!
      if(idx != (var_t) -1) {
        const xcls_watch& r_cls2 = xclss[idx];
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
          VERB(120, "c resolving clauses\nc   "<< BOLD(r_cls.to_str()) <<"\nc and\nc   "<< BOLD(r_cls2.to_str()));
          r_cls.resolve(r_cls2, alpha, alpha_dl, alpha_trail_pos, dl_count);
          VERB(120, "c and get \nc   "<< BOLD(r_cls.to_str()));
        #ifndef NDEBUG
          VERB(120, "c tmp = "<<tmp.to_str());
        #endif
          VERB(120, "c");
          assert( !L_.is_consistent() || L_.reduce(tmp+r_cls2.get_unit()).is_zero() );
          assert(r_cls.to_xcls().reduced(alpha).is_unit());
          assert( !L_.is_consistent() || L_.reduce( r_cls.to_xcls().reduced(alpha).get_unit()+tmp).is_constant() );
        }
      }

      return r_cls.finalize(alpha_dl, alpha_trail_pos, dl_count, max_size);
    }

    /**
     * @brief construct reason cls by resolving list of xclss; new clause is added to xclss
     * @note same as 'get_reason_and_init()', but const!
     * 
     * @param rs_cls_idxs list of linerals whose reasons to resolve
     * @param add_idx additional index to resolve with
     * @param max_size maximal size in each filtration level, (var_t) -1 for default heuristic
     * @return var_t indedx position of new xcls_watch
     */
    inline xcls_watch get_reason(const list<xlit_w_it>& rs_cls_idxs, const var_t idx = (var_t) -1, const var_t max_size = (var_t) -1) const {
    #ifdef DEBUG_SLOW
      auto L_ = get_lineral_watches_xsys();
      xlit tmp;
    #endif
      //resolve cls to get true reason cls
      xcls_watch_resolver r_cls;
      {
      xcls_watch r_cls2;
      for(const auto& lin : rs_cls_idxs) {
        if(r_cls.is_zero()) { //r_cls has not yet been instantiated
          r_cls = get_reason(lin);
          assert(r_cls.is_unit(dl_count));
        } else {
          r_cls2 = get_reason(lin);
          //resolve cls
          assert(r_cls2.is_unit(dl_count));
        #ifndef NDEBUG
          xlit unit = r_cls2.get_unit();
        #endif
          //extend r_cls2 with (unit of r_cls)+1, and r_cls with (unit of r_cls2)+1
          VERB(120, "c resolving clauses\nc   "<< BOLD(r_cls.to_str()) <<"\nc and\nc   "<< BOLD(r_cls2.to_str()));
          r_cls.resolve( std::move(r_cls2), alpha, alpha_dl, alpha_trail_pos, dl_count);
          VERB(120, "c and get \nc   "<< BOLD(r_cls.to_str()));
          VERB(120, "c");
          assert_slow( !L_.is_consistent() || L_.reduce(tmp+unit).is_zero() );
          assert(r_cls.to_xcls().reduced(alpha).is_unit());
          assert_slow( !L_.is_consistent() || L_.reduce( r_cls.to_xcls().reduced(alpha).get_unit()+tmp).is_constant() );
        }
      }
      }
      //resolve with additional clause -- if required!
      if(idx != (var_t) -1) {
        const xcls_watch& r_cls2 = xclss[idx];
        if(r_cls.is_zero()) { //r_cls has not yet been instantiated
          r_cls = r_cls2;
          assert(r_cls.is_unit(dl_count));
        } else {
          //resolve cls
          assert(r_cls2.is_unit(dl_count));
          //extend r_cls2 with (unit of r_cls)+1, and r_cls with (unit of r_cls2)+1
          VERB(120, "c resolving clauses\nc   "<< BOLD(r_cls.to_str()) <<"\nc and\nc   "<< BOLD(r_cls2.to_str()));
          r_cls.resolve(r_cls2, alpha, alpha_dl, alpha_trail_pos, dl_count);
          VERB(120, "c and get \nc   "<< BOLD(r_cls.to_str()));
          VERB(120, "c");
          assert_slow( !L_.is_consistent() || L_.reduce(tmp+r_cls2.get_unit()).is_zero() );
          assert(r_cls.to_xcls().reduced(alpha).is_unit());
          assert_slow( !L_.is_consistent() || L_.reduce( r_cls.to_xcls().reduced(alpha).get_unit()+tmp).is_constant() );
        }
      }

      return r_cls.finalize(alpha_dl, alpha_trail_pos, dl_count, max_size);
    }

    inline xcls_watch& get_reason_and_init(xlit_w_it lin, var_t max_size = (var_t)-1) {
      VERB(120, "c constructing reason clause for "<<lin->to_str());

      //note, returning zero_cls might lead to complications!
      if(!lin->has_trivial_reason_cls() && lin->get_reason_lins().empty() && lin->get_reason_idx() != (var_t)-1) return xclss[lin->get_reason_idx()];

      //construct reason clause
      const auto rs = lin->has_trivial_reason_cls() ? xcls_watch( (xlit) *lin, alpha, alpha_dl, alpha_trail_pos, dl_count) : get_reason_and_init( lin->get_reason_lins(), lin->get_reason_idx(), max_size);
      assert_slow(!rs.is_zero());

      //place rs into xclss
      xclss.emplace_back( std::move(rs) );
      utility.emplace_back( 0 );
      const var_t i = xclss.size()-1;
      //set redundancy
      xclss[i].set_redundancy(true);
      // add new cls to watch_lists
      if(xclss.back().size()>0) watch_list[ (xclss.back().get_wl0()) ].emplace_back(i);
      if(xclss.back().size()>1) watch_list[ (xclss.back().get_wl1()) ].emplace_back(i);
      //adapt reason of lin
      lin->clear_reason_idxs();
      lin->push_reason_idx( i );
      
      assert_slow(xclss[i].is_unit(dl_count) && (xclss[i].get_unit().reduced(alpha,equiv_lits)+lin->to_xlit().reduced(alpha,equiv_lits)).reduced(alpha,equiv_lits).is_zero());
      return xclss[i];
    }
    
    inline xcls_watch get_reason(const xlit_w_it lin, var_t max_size = (var_t)-1) const {
      VERB(120, "c constructing reason clause for "<<lin->to_str());

      if(lin->has_trivial_reason_cls()) {
        return xcls_watch( (xlit) *lin, alpha, alpha_dl, alpha_trail_pos, dl_count);
      }
      if(lin->get_reason_lins().empty() && lin->get_reason_idx() != (var_t) -1) {
        const auto rs = xclss[lin->get_reason_idx()];

        assert_slow(rs.is_unit(dl_count) && (rs.get_unit()+lin->to_xlit()).reduced(alpha).is_zero());
        assert(rs.is_unit(dl_count) && rs.get_unit().reduced(alpha)==lin->to_xlit().reduced(alpha));

        return rs;
      }

      //construct reason clause
      const auto rs = get_reason( lin->get_reason_lins(), lin->get_reason_idx(), max_size );
      
      //assert_slow(rs.is_unit(dl_count) && (rs.get_unit()+lin->to_xlit()).reduced(alpha).is_zero());
      assert(rs.is_unit(dl_count) && rs.get_unit().reduced(alpha)==lin->to_xlit().reduced(alpha));

      return rs;
    }
    
    inline xcls_watch& get_reason_and_init(const trail_elem& t, var_t max_size = (var_t)-1) {
      return get_reason_and_init(t.lin, max_size);
    }
    
    inline xcls_watch get_reason(const trail_elem& t, var_t max_size = (var_t)-1) const {
     #ifndef NDEBUG
      auto rs = get_reason(t.lin, max_size);
      assert( at_conflict() || rs.assert_data_struct(alpha, alpha_trail_pos, dl_count) );
      return rs;
     #else
      return get_reason(t.lin, max_size);
     #endif
    }

    typedef xlit (solver::*dec_heu_t)();
    typedef std::pair<var_t,xcls_watch> (solver::*ca_t)(solver&);

    void bump_score(const var_t& ind);
    void bump_score(const xlit& lit);
    void decay_score();
    
    inline void add_new_guess(xlit l) {
      //update assignments
      lineral_watches[dl].emplace_back( l, alpha, alpha_dl, dl_count, dl );
      queue_implied_lineral( std::prev(lineral_watches[dl].end()), dl, queue_t::NEW_GUESS);
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
     #if !defined(NDEBUG) && defined(DEBUG_SLOWER)
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
     * @param lin iterator to xlit_watch in lineral_watches
     * @param lvl dl-level on which to propagate lin
     * @param type tral_t of lineral specifying type of propagation
     * @todo write seperate funcs for types: NEW_UNIT, IMPLIED_ALPHA and NEW_GUESS
     * 
     * @return var_t ind>=0 iff alpha[ind] is now assigned; ind==-1 means no new alpha-assignment
     */
    inline var_t process_lineral(xlit_w_it lin, const var_t lvl, const queue_t type = queue_t::NEW_UNIT) {
      assert(lvl >= lin->get_lvl());
      VERB(65, "c " << std::to_string(lvl) << " : process_lineral " << type << lin->to_str() << " ~> " << lin->to_xlit().reduced(alpha,equiv_lits).to_str() << (lin->has_trivial_reason_cls() ? "" : (" with reason clause " + get_reason(lin, 1).to_str())) );
      if(lin->is_reducible() && type!=queue_t::IMPLIED_ALPHA) {
        assert(lvl==lin->get_lvl());
        //reduce lin -- but only if type is NOT guess -- otherwise reason clause is not computed correctly!
        assert_slow(lvl==0 || get_reason(lin).get_unit().reduced(alpha)==lin->to_xlit().reduced(alpha));
        if(opt.eq && type!=queue_t::NEW_GUESS) lin->reduce(alpha, alpha_dl, dl_count, equiv_lits, lvl);
        else                                   lin->reduce(alpha, alpha_dl, dl_count, lvl);
        assert_slow(lvl==0 || lin->is_zero() || get_reason(lin).get_unit().reduced(alpha)==lin->to_xlit().reduced(alpha));
      }
      if(lin->is_zero(alpha)) {
        if(lin->is_zero()) lineral_watches[lvl].erase( lin ); //remove lin when it is zero on its respective level
        return -1;
      }
      
      //TODO should we always reduce?! consider the following:
      //we already have UNIT x1+x2+x3 and now get x1; full reduction would give x2+x3, even though x1 would be assigning!
      //DO NOT REDUCE WITH TOO LONG XORs otherwise it might blow up!
      //@todo heuristically reduce less active variables; i.e. decrease number of 'inactive' vars and increase the active ones

      xlit_watch& l = *lin;

      //add to watch list if non-assigning AND not 'IMPLIED_ALPHA' (since this means it comes from a already watched lineral!)
      if(type!=queue_t::IMPLIED_ALPHA && !l.is_assigning()) {
        assert(l.size()>1);
        L_watch_list[ l.get_wl0() ].emplace_back( lvl, dl_count[lvl], lin );
        L_watch_list[ l.get_wl1() ].emplace_back( lvl, dl_count[lvl], lin );
        assert_slow( l.size()==0 || lin->watches( l.get_wl0() ) || lin->to_xlit().is_constant() );
        assert_slow( l.size()<=1 || lin->watches( l.get_wl1() ) || lin->to_xlit().is_constant() );
      }

      if(l.is_active(alpha)) {
        if(opt.eq && l.is_equiv()) {
          //if l is equiv!
          const var_t lt = l.LT();
          const var_t lt_other = l.get_equiv_lit();
          assert(lt < lt_other ); //ensure that lt is smallest!
          assert(!equiv_lits[lt].is_active()); //ensure that lt does not already have an equiv literal
          //add to equiv_lits
          equiv_lits[lt].set_ind( lt_other );
          equiv_lits[lt].set_lvl( lvl );
          equiv_lits[lt_other].set_prev_ind( lt );
          equiv_lits[lt].set_polarity( l.has_constant() );
          equiv_lits[lt].set_lin( lin );
          lin->set_reducibility(false);
          assert( l.get_equiv_lvl(alpha_dl) <= lvl );
          //add to trail
          trails[lvl].emplace_back( lt, trail_t::EQUIV, lin );
          VERB(65, "c " << std::to_string(lvl) << " : new EQUIV " << l.to_str() )
          //if we learn the equiv on lvl 0, schedule remove_fixed_equiv with next GCP on dl 0
          if(lvl==0) {
            remove_fixed_equiv_before_next_GCP = true;
            l.clear_reason_lins();
          }
        } else {
          assert(type==queue_t::NEW_UNIT || type==queue_t::NEW_GUESS);
          //only add to trail when it is a GUESS - learning only requires the lite literal trail
          //trails[lvl].emplace_back( l.LT(), type==queue_t::NEW_GUESS ? trail_t::GUESS : trail_t::UNIT, lin);
          if(type==queue_t::NEW_GUESS) {
            trails[lvl].emplace_back( l.LT(), trail_t::GUESS, lin);
          }
        }
        return -1;
      }
      
      //rm reasons on dl 0 -- might simplify conflict resolution on higher dls (esp with many implications on dl 0)
      //@todo clear reason right after reduction?!
      if(lvl==0) l.clear_reason_lins();

      //now l must be an alpha-assignment!
      assert(l.is_assigning(alpha));
      const var_t assigning_lvl = std::max(lvl, l.get_assigning_lvl(alpha_dl));
      //if assignment on higher dl (e.g. when learning UNIT on prev dl + reduction with other lins leads to assignment!), backtrack properly!
      VERB(70, "c " << std::to_string(assigning_lvl) << " : new ALPHA " << l.get_assigning_xlit(alpha).to_str() << " from UNIT " << l.to_str() << (type!=queue_t::NEW_GUESS  && !lin->has_trivial_reason_cls() && assigning_lvl>0 ? (" with reason clause " + get_reason(lin).to_str()) : "") );
      if(assigning_lvl < dl){
        VERB(70, "c " << std::to_string(assigning_lvl) << " : backtracking to " << std::to_string(assigning_lvl) << " as ALPHA was obtained on lower dl!" );
        backtrack(assigning_lvl);
        assert(dl==assigning_lvl);
        assert(opt.eq); //this can only happen when equivalence reductions are activated!
      }
      //get alpha-assignment
      const auto [lt2,val] = l.get_assignment(alpha);
      assert(l.is_assigning(alpha) && val!=bool3::None);
      trails[assigning_lvl].emplace_back( lt2, trail_t::ALPHA, lin );
      l.set_reducibility(false);
      assert( alpha[lt2]==val || alpha[lt2]==bool3::None );
      alpha[lt2] = val;
      alpha_dl[lt2] = assigning_lvl;
      assert(lt2==0 || alpha_dl[lt2] == std::max(l.get_assigning_lvl(alpha_dl), lvl));
      assert(alpha_trail_pos[lt2] == (var_t) -1);
      alpha_trail_pos[lt2] = stepwise_lit_trail_length;
      ++stepwise_lit_trail_length;
      assert(type==queue_t::NEW_GUESS || !lin->is_reducible() || equiv_lits[lt2].ind==0 || alpha[equiv_lits[lt2].ind]!=bool3::None);
      return lt2;
    };

    /**
     * @brief queue implied lineral for propagation (one-by-one); update data using propagate_implied_lineral
     * @note highest priority is conflict, followed by alpha and then equivs
     * 
     * @param lin lineral to be added to data structures
     * @param lvl dl-level on which lin should be propagated as 'type'
     * @param type type of propagation (defaults to queue_t::NEW_UNIT)
     */
    inline void queue_implied_lineral(xlit_w_it lin, const var_t lvl, const queue_t type = queue_t::NEW_UNIT) {
      assert(lin->assert_data_struct(alpha));
      if(type==queue_t::NEW_GUESS) lineral_queue.q_alpha.emplace_front( lin, lvl, type );
      else if(lin->LT()==0) {
        lineral_queue.q_confl.emplace_front( lin, lvl, queue_t::IMPLIED_ALPHA );
      } else if(lin->is_assigning(alpha)) {
        lineral_queue.q_alpha.emplace_back( lin, lvl, type );
      } else if(opt.eq && lin->is_equiv()) {
        //TODO check if is_equiv() or is_equiv(alpha) performs better! -- the latter can increase the LBD of reason clause!
        lineral_queue.q_equiv.emplace_back( lin, lvl, type );
      } else {
        lineral_queue.q_unit.emplace_back( lin, lvl, type );
      }
    }
    
    /**
     * @brief queue implied lineral for propagation (one-by-one); update data using propagate_implied_lineral
     * 
     * @param ind var-idx to be assigned
     * @param bool3 val value of alpha-assignment
     * @param rs rs_cls_idx of reason clause
     * @param type type of propagation (defaults to trail_t::NEW_ALPHA)
     */
    //@todo remove this func!
    inline void queue_implied_alpha(xlit_w_it lin) {
      //[[maybe_unused]] const auto lt = lin->is_constant() ? 0 : lin->get_wl1();
      //assert(alpha[lt] == bool3::None || alpha[lt] == lin->get_assigning_val(alpha));
      queue_implied_lineral(lin, dl, queue_t::IMPLIED_ALPHA);
    }

    /**
     * @brief propagates lineral from queue until a new alpha is propagated or the queue is empty
     * 
     * @return var_t idx of new lt; or -1 if no new alpha was propagated
     */
    inline var_t propagate_implied_lineral() {
      assert(!lineral_queue.empty());
      auto& [lin, lvl, type] = lineral_queue.front();
      var_t new_lt = process_lineral(lin, lvl, type);
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
    double avg_la_per_sec = 0;
    var_t checks_until_next_la = 1 << 7;
    long gauss_elim_schedule_wait = 1 << 7;
    /**
     * @brief decides whether a Gaußian Elimination in-processing step should be performed
     * 
     * @param stats s current stats
     */
    inline bool need_ge_inprocessing(stats& s) {
      if(at_conflict() || opt.gauss_elim_schedule==0) return false;
      else if(dl==0) return true; //always use linear algebra on dl 0?
      else if(opt.gauss_elim_schedule==-1) {
        //adaptive scheduling: decrease gauss_elim_schedule, if average usability decreased
        --checks_until_next_la;
        if(checks_until_next_la!=0) return false;
        double new_avg = (double) ( (s.no_ge_prop) / (s.total_linalg_time.count()) + avg_la_per_sec ) / 2;
        if(gauss_elim_schedule_wait==1 || avg_la_per_sec >= new_avg) {
          gauss_elim_schedule_wait += 1;
          VERB(10, "c new_avg: " << std::to_string(new_avg) );
          VERB(10, "c increasing gauss_elim_schedule_wait to " << std::to_string(gauss_elim_schedule_wait))
        } else {
          gauss_elim_schedule_wait = gauss_elim_schedule_wait>1 ? gauss_elim_schedule_wait-1 : 1;
          VERB(10, "c new_avg: " << std::to_string(new_avg) );
          VERB(10, "c decreasing gauss_elim_schedule_wait to " << std::to_string(gauss_elim_schedule_wait))
        }
        avg_la_per_sec = new_avg;
        checks_until_next_la = gauss_elim_schedule_wait;
        return true;
      }
      ++ctr;
      ctr %= opt.gauss_elim_schedule;
      return ctr == 0 && !at_conflict();
    }

    /**
     * @brief get all implied alpha's from lineral assignments
     * @note might backtrack if a propagation on a lower dl is noticed!
     * 
     * @return true iff a new forcing lineral/equivalence was found
     */
    bool find_implications_by_GE(stats& s) {
      const auto begin  = std::chrono::high_resolution_clock::now();
      ++s.no_ge;
    #ifndef NDEBUG
      vec<xlit> lits; lits.reserve(lineral_watches.size());
      for(const auto& l_dl : lineral_watches) {
          for(const auto& l : l_dl) lits.emplace_back( l.to_xlit() );
      }
      xsys L_( std::move(lits) );
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
      list<xlit> xlits_;
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
          assert(xlits_.size()==0);
          assert(mzd_read_bit(M,r,n_vars));
          xlits_.emplace_back( 0, false );
          break;
        } else if(idxs.size()==1 && alpha[idxs[0]]!=to_bool3(mzd_read_bit(M,r,n_vars)) ) {
          xlits_.emplace_back( idxs[0], (bool) mzd_read_bit(M, r, n_vars) );
        } else if(idxs.size()==2 && equiv_lits[idxs[0]].ind==0 && opt.eq) {
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
        const auto end  = std::chrono::high_resolution_clock::now();
        s.total_linalg_time += std::chrono::duration_cast<std::chrono::duration<double>>(end - begin);
        return false;
      }

      mzd_t* B = mzd_init(std::max(ncols,nrows), xlits_.size());
      VERB(80, "c found "<<std::to_string(xlits_.size())<<" new alpha assignments and equivs");
      idx = 0;
      for(const auto& lit : xlits_) {
        VERB(85, "c   `--> " << lit.to_str());
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
       s.no_ge_prop += xlits_.size();

      //construct corresponding reason clauses
      idx = 0;
      for(auto&& lit : xlits_) {
        VERB(95, "c constructing reason cls indices for "<<lit.to_str());
        
        list<xlit_w_it> r_cls_idxs;
        var_t resolving_lvl = 0;
      
      #ifndef NDEBUG
        xlit tmp;
      #endif
      #ifdef DEBUG_SLOWER
        r=0;
        for(var_t lvl=0; lvl<=dl; ++lvl) {
          auto& l_dl = lineral_watches[lvl];
          //check solution:
          for(xlit_w_it l_it = l_dl.begin(); l_it != l_dl.end() && r < B->nrows; ++l_it, ++r) {
            if(!mzd_read_bit(B,r,idx)) continue;
            tmp += *l_it;
          }
        }
        assert(L_.reduce(tmp+lit).is_zero());
        tmp.clear();
      #endif
        assert( L_.reduce(tmp+lit).is_zero() );
        
        r = 0;
        for(var_t lvl=0; lvl<=dl; ++lvl) {
          auto& l_dl = lineral_watches[lvl];
          if(l_dl.empty()) continue;
          for(xlit_w_it l_it = l_dl.begin(); l_it != l_dl.end() && r < B->nrows; ++l_it, ++r) {
            if(!mzd_read_bit(B,r,idx)) continue;
          #ifndef NDEBUG
            tmp += *l_it;
            assert( L_.reduce(tmp+lit).is_zero() );
          #endif
            resolving_lvl = lvl;
            bump_score(*l_it);
            //add all linerals EXCEPT when they come from NEW_GUESS, i.e., are the first lin in l_dl (the 'is_assigning' condition is a workaround to avoid asserts to fail in 'minimize'-calls!)
            if(lvl==0 || l_it!=l_dl.begin() || !l_it->is_assigning()) {
              r_cls_idxs.emplace_back( l_it );
            }
          }
        }
        //post-process r_cls_idxs -- so far r_cls_idxs will lead to a reason clause that ONLY contains GUESS variables; which is potentially cumbersome -- thus: remove all assigning linerals from 'inbetween' decisions-levels
        if(resolving_lvl==0) r_cls_idxs.clear();
        r_cls_idxs.remove_if([resolving_lvl](const auto lin){ return lin->get_lvl()!=0 && lin->get_lvl()!=resolving_lvl && lin->is_assigning(); });

        assert((tmp+lit).reduced(alpha).is_zero());
        ++idx;
        //add lineral to lineral_watches
        const bool equiv = lit.is_equiv();
        lineral_watches[resolving_lvl].emplace_back( std::move(lit), alpha, alpha_dl, dl_count, std::move(r_cls_idxs), resolving_lvl );

      #ifndef NDEBUG
        const auto lin = std::prev(lineral_watches[resolving_lvl].end());
        [[maybe_unused]] const auto rcls = get_reason(lin);
        //ensure that reason cls is reason for provided alpha AND equiv_lits
        assert_slow(rcls.is_unit(dl_count) && (rcls.get_unit()+lin->to_xlit()).reduced(alpha,equiv_lits).is_zero());
        //ensure that reason cls is reason for provided alpha
        assert(rcls.is_unit(dl_count) && (rcls.get_unit()+lin->to_xlit()).reduced(alpha).is_zero());
      #endif

        //backtrack if necessary!
        if(resolving_lvl < dl) {
          backtrack(resolving_lvl);
          assert(resolving_lvl==dl);
          queue_implied_lineral(std::prev(lineral_watches[dl].end()), dl, equiv ? queue_t::NEW_EQUIV : queue_t::NEW_UNIT);
          //return immediately
          break;
        }
        assert(resolving_lvl==dl);
        queue_implied_lineral(std::prev(lineral_watches[dl].end()), dl, equiv ? queue_t::NEW_EQUIV : queue_t::NEW_UNIT);
      }

      mzd_free(B);
      mzd_free(M_tr);
      
      const auto end  = std::chrono::high_resolution_clock::now();
      s.total_linalg_time += std::chrono::duration_cast<std::chrono::duration<double>>(end - begin);

      return true;
    }

    /**
     * @brief triangulates watched linerals; i.e. updates them w.r.t. previous linerals and brings them in non-reduced row-echelon form
     * @note we cannot reuse the code from find_implications_by_GE or from check_lineral_watches_GE, since this function should be 'const'!
     */
    inline xsys get_lineral_watches_xsys() const {
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
      
      //mzd_print(M);
      //read results
      list<xlit> xlits_;
      vec<var_t> idxs;
      for(rci_t r = 0; r<rank; ++r) {
        idxs.clear();
        for(rci_t c=0; (unsigned)c<n_vars; ++c) {
            if( mzd_read_bit(M, r, c) ) idxs.push_back(perm_inv[c]);
        }
        xlits_.emplace_back( std::move(idxs), (bool) mzd_read_bit(M, r, n_vars), presorted::yes );
      }

      xsys L = xsys( std::move(xlits_) );
      assert( L_.to_str() == L.to_str() );
      VERB(80, "c reduction done.");

      mzd_free(M);
      mzd_free(M_tr);
      
      return L;
    };

    /**
     * @brief checks if lineral watches imply a conflict -- and if so  triangulates watched linerals; i.e. updates them w.r.t. previous linerals and brings them in non-reduced row-echelon form
     * 
     * @return L,cls where L is the xsys of all watched linerals and if L is inconsistent then cls is a conflict clause
     */
    inline std::tuple<xsys,xcls_watch> check_lineral_watches_GE() {
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
      list<xlit> xlits_;
      vec<var_t> idxs;
      for(rci_t r = 0; r<rank; ++r) {
        idxs.clear();
        for(rci_t c=0; (unsigned)c<n_vars; ++c) {
            if( mzd_read_bit(M, r, c) ) idxs.push_back(perm_inv[c]);
        }
        xlits_.emplace_back( std::move(idxs), (bool) mzd_read_bit(M, r, n_vars), presorted::yes );
      }

      xsys L = xsys( std::move(xlits_) );
      assert( L_.to_str() == L.to_str() );
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
      
      r = 0;
      //resolve cls to get true reason cls
      list<xlit_w_it> r_cls_idxs;
    
    #ifndef NDEBUG
      xlit tmp;
    #endif
    #ifdef DEBUG_SLOWER
      r=0;
      for(var_t lvl=0; lvl<=dl; ++lvl) {
        auto& l_dl = lineral_watches[lvl];
        //check solution:
        for(xlit_w_it l_it = l_dl.begin(); l_it != l_dl.end() && r < b->nrows; ++l_it, ++r) {
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
        for(xlit_w_it l_it = l_dl.begin(); l_it != l_dl.end() && r < b->nrows; ++l_it, ++r) {
          if(!mzd_read_bit(b,r,0)) continue;
        #ifndef NDEBUG
          tmp += *l_it;
          assert( L_.reduce(tmp).is_zero() );
        #endif
          resolving_lvl = lvl;
          bump_score(*l_it);
          //add all linerals EXCEPT when they come from NEW_GUESS, i.e., are the first lin in l_dl (the 'is_assigning' condition is a workaround to avoid asserts to fail in 'minimize'-calls!)
          if(lvl==0 || l_it!=l_dl.begin() || !l_it->is_assigning()) {
            r_cls_idxs.emplace_back( l_it );
          }

          #ifndef NDEBUG
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
      
      list<xlit_watch> tmp_l;
      tmp_l.emplace_back( xlit(0,false), alpha, alpha_dl, dl_count, std::move(r_cls_idxs), resolving_lvl );
      const auto lin = tmp_l.begin();

      mzd_free(b);
      mzd_free(M_tr);

    #ifndef NDEBUG
      const auto reason_cls = get_reason( lin );
      //ensure that reason cls is reason for provided alpha
      assert_slow(reason_cls.is_unit(dl_count) && reason_cls.get_unit().reduced(alpha).is_one());
    #endif

      return {L, get_reason( lin ) };
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
      assert( !cls.is_zero() );
      xcls_watch cls_w( std::move(cls) );
      cls_w.init(alpha, alpha_dl, alpha_trail_pos, dl_count);
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
      //update cls
      VERB(90, "c adding new clause: " << BOLD(xclss[i].to_str()) << "  --> gives with current assignments: "<<xclss[i].to_xcls().reduced(alpha).to_str());
      if(learnt_cls) VERB(90, "c XNF : " << xclss[i].to_xnf_str());
      const auto ret = learnt_cls ? xcls_upd_ret::UNIT : xclss[i].init(alpha, alpha_dl, alpha_trail_pos, dl_count);
      //adapted from GCP
      switch (ret) {
      case xcls_upd_ret::SAT:
          assert(!learnt_cls);
          assert(xclss[i].is_sat(dl_count));
          assert(xclss[i].is_inactive(dl_count));
          // IGNORE THIS CLAUSE FROM NOW ON
          decr_active_cls(i);
          break;
      case xcls_upd_ret::UNIT: //includes UNSAT case (i.e. get_unit() reduces with assignments to 1 !)
      {
          assert(xclss[i].is_unit(dl_count));
          assert(xclss[i].is_inactive(dl_count));
          //update utility
          ++utility[i];
          //utility[i] = -xclss[i].LBD(alpha_dl);
          // IGNORE THIS CLAUSE FROM NOW ON
          decr_active_cls(i);
          // NEW LIN-EQS
          //add on respective lvl!
          const var_t lvl = xclss[i].get_unit_at_lvl();
          lineral_watches[lvl].emplace_back( std::move(xclss[i].get_unit()), alpha, alpha_dl, dl_count, i, lvl);
          queue_implied_lineral( std::prev(lineral_watches[lvl].end()), lvl, queue_t::NEW_UNIT );
          break;
      }
      case xcls_upd_ret::NONE:
          assert(!learnt_cls); //must not happen for learnt clauses
          assert(xclss[i].is_none(dl_count));
          assert(xclss[i].is_active(dl_count));
          break;
      }
      //clause only needs to be watched, if it has size()>1 (!)
      if(xclss[i].size()>1) {
        watch_list[ (xclss[i].get_wl0()) ].emplace_back(i);
        watch_list[ (xclss[i].get_wl1()) ].emplace_back(i);
      }
      // add new cls to watch_lists
      assert( !xclss[i].to_xcls().is_zero() );
      assert( xclss[i].assert_data_struct(alpha, alpha_trail_pos, dl_count) );
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

    //copy ctor -- re-adds all clauses, i.e., looses precise state of watched vars and trail; but keeps activity_score and utility!
    solver(const solver& o) noexcept : opt(o.opt), activity_score(o.activity_score), dl_count(o.dl_count), last_phase(o.last_phase) { 
      opt.verb = 0;
      backtrack(0);
      // init data structures
      const auto num_vars = o.get_num_vars();
      //init watch_list
      watch_list.resize(num_vars+1);
      L_watch_list.resize(num_vars+1);
      lineral_watches = vec<list<xlit_watch>>(num_vars+1, list<xlit_watch>() );
    
      // init assignments
      alpha = vec<bool3>(num_vars + 1, bool3::None);
      alpha_dl = vec<var_t>(num_vars + 1, (var_t) -1);
      alpha_trail_pos = vec<var_t>(num_vars + 1, (var_t) -1);
      equiv_lits = vec<equivalence>(num_vars+1);
      dl_count = vec<dl_c_t>(num_vars+1, 1); 
      trails = vec< list<trail_elem> >();
      trails.reserve(num_vars+1);
      trails.emplace_back( list<trail_elem>() );
      stepwise_lit_trail_length = 1;

      //re-add all clauses
      vec< xcls > xclss_; xclss_.reserve(o.xclss.size());
      for(const auto& cls : o.xclss) xclss_.emplace_back( std::move(cls.to_xcls()) );
      init_xclss( xclss_ );
      
      for(var_t i = 1; i<=num_vars; ++i) {
          order_heap_vsids.insert( i );
      }

      //init restart params
      update_restart_schedule(0);

      assert(assert_data_structs());
    };

    ~solver() = default;

    /**
     * @brief init solver
     * 
     * @param clss vector of xcls
     */
    void init_xclss(const vec< xcls >& clss) noexcept;


    void remove_fixed_alpha(const var_t upd_lt);

    bool remove_fixed_equiv_before_next_GCP = false;
    void remove_fixed_equiv();
    
    void GCP(stats& s) noexcept;

    /**
     * @brief performs linear algebra in-processing;
     * @note only call this on dl 0!
     * 
     * @param s stats
     * @return bool true iff new clauses were added, and new alpha assignments derived
     */
    bool initial_linalg_inprocessing(stats& s) {
      assert(dl==0);
      if( !need_ge_inprocessing(s) ) return false;
      return find_implications_by_GE(s);
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

    solver& operator=(const solver& ig) = default;

    bool assert_data_structs() const noexcept;
    void print_trail(std::string lead = "") const noexcept;

};