#pragma once

#include <stack>
#include <math.h>
#include <map>
#include <list>
#include <queue>
#include <memory>
#include <array>
#include <sstream>

#include "misc.hpp"
#include "io.hpp"
#include "lineral.hpp"
#include "lineral_watch.hpp"
#include "lin_sys.hpp"
#include "lin_sys_lazy.hpp"
#include "cls.hpp"
#include "cls_watch.hpp"
#include "cls_watch_resolver.hpp"
#include "order_heap/heap.h"

#include "xornado/impl_graph.hpp"

#define TRAIL trails.back()

using lin_w_it = list<lineral_watch>::iterator;

enum class trail_t { GUESS, ALPHA, EQUIV, UNIT };

enum class queue_t { NEW_GUESS, IMPLIED_ALPHA, NEW_UNIT };
    
enum class origin_t { GUESS, CLAUSE, LINERAL, LGJ, IG, INIT };

std::ostream& operator<<(std::ostream& os, const trail_t& t);

std::ostream& operator<<(std::ostream& os, const queue_t& t);

std::ostream& operator<<(std::ostream& os, const origin_t& t);

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
   * @brief origin of trail elem
   */
  origin_t origin;
  /**
   * @brief pointer to associated lineral_watch
   */
  lin_w_it lin;

  trail_elem() : ind(0) {};
  trail_elem(const var_t& _ind, const trail_t& _type, const origin_t& _origin, lin_w_it _lin) : ind(_ind), type(_type), origin(_origin), lin(_lin) {};
  trail_elem(const trail_elem& other) : ind(other.ind), type(other.type), origin(other.origin), lin(other.lin) {};
  trail_elem(trail_elem&& other) : ind(other.ind), type(other.type), origin(other.origin), lin(other.lin) {};

  constexpr trail_elem& operator=(const trail_elem& o) = default;
  
  void swap(trail_elem& o) noexcept {
    std::swap(ind, o.ind);
    std::swap(type, o.type);
    std::swap(origin, o.origin);
    std::swap(lin, o.lin);
  };
};

struct lineral_queue_elem {
  /**
   * @brief lineral to 'propagate'/'add'
   */
  lin_w_it lin;
  /**
   * @brief decision-level on which to propagate
   */
  var_t lvl;
  /**
   * @brief type of propagation: 'NEW_UNIT': reduce newly learnt unit + watch; 'NEW_GUESS': add new guess + watch; 'IMPLIED_UNIT': update alpha/alpha_dl data structures;
   */
  queue_t type;
  /**
   * @brief type of origin
   */
  origin_t origin;

  lineral_queue_elem() : lin(), lvl((var_t) -1), type(queue_t::NEW_UNIT), origin(origin_t::CLAUSE) {};
  lineral_queue_elem(lin_w_it _lin, const var_t _lvl, const queue_t& _type, const origin_t& _origin) : lin(_lin), lvl(_lvl), type(_type), origin(_origin) {};
  lineral_queue_elem(const lineral_queue_elem& other) = default;
  lineral_queue_elem(lineral_queue_elem&& other) = default;
};

//wrapper class that concats four queues
template<class T>
class lin_queue {
  //lin_queue structure: CONFL | IMPLIED_ALPHA | LGJ_IMPLIED_ALPHA | NEW_EQUIV |  NEW_UNIT
  public:
    list<T> q_confl;
    list<T> q_alpha;
    list<T> q_lgj;
    list<T> q_equiv;
    list<T> q_unit;

    lin_queue() noexcept {};

    size_t size() const { return q_confl.size()+q_alpha.size()+q_lgj.size()+q_equiv.size()+q_unit.size(); };
    bool empty() const { return q_confl.empty() && q_alpha.empty() && q_lgj.empty() && q_equiv.empty() && q_unit.empty(); };

    deque<T>::reference front() {
      //when changing order here, reflect the cahnge in pop_front() as well!
      assert(!empty());
      if(!q_confl.empty())          return q_confl.front();
      else if(!q_alpha.empty())     return q_alpha.front();
      else if(!q_lgj.empty())       return q_lgj.front();
      else if(!q_equiv.empty())     return q_equiv.front();
      else                          return q_unit.front();
    };

    void pop_front() {
      //when changing order here, reflect the cahnge in front() as well!
      assert(!empty());
      if(!q_confl.empty())          q_confl.pop_front();
      else if(!q_alpha.empty())     q_alpha.pop_front();
      else if(!q_lgj.empty())       q_lgj.pop_front();
      else if(!q_equiv.empty())     q_equiv.pop_front();
      else                          q_unit.pop_front();
    };
    
    /**
     * @brief clear all els in queue with too high level
     * 
     * @param lvl max lvl that is allowed in queue
     */
    void clear(const var_t lvl) {
      q_confl.remove_if([lvl](const auto& q_el){ return q_el.lvl > lvl; });
      q_alpha.remove_if([lvl](const auto& q_el){ return q_el.lvl > lvl; });
      q_lgj.remove_if(  [lvl](const auto& q_el){ return q_el.lvl > lvl; });
      q_equiv.remove_if([lvl](const auto& q_el){ return q_el.lvl > lvl; });
      q_unit.remove_if( [lvl](const auto& q_el){ return q_el.lvl > lvl; });
    }

    void clear() {
      q_confl.clear();
      q_alpha.clear();
      q_lgj.clear();
      q_equiv.clear();
      q_unit.clear();
    }
};

struct watch_list_elem {
  var_t lvl;
  dl_c_t dl_c;
  lin_w_it lin;
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
  friend cls_watch_resolver;
  private:
    /**
     * @brief xor-clause watchers
     */
    vec< cls_watch > xnf_clss;

    /**
     * @brief utility[i] gives number of unit propagations of clss[i] (with moving average) @todo fix this line!!
     */
    vec<double> utility;
    double util_cutoff; //min utility to keep a clause on cleanup

    /**
     * @brief watch_list[i] contains all idxs j s.t. clss[j] watches indet i
     */
    vec< vec<var_t> > watch_list;
    
    /**
     * @brief L_watch_list[lt] stores elements of the form [lvl, dl_c, lin]; indicating that lt is watched in *lin IFF dl_count[lvl]==dl_c
     */
    vec< vec< watch_list_elem > > L_watch_list;

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
    Heap<VarOrderLt> order_heap_vsids{ VarOrderLt(activity_score) };

    /**
     * @brief counts how often a dl was visited -- required to quickly discard lineral that were already watched previously in the current search tree
     *        dl_count[i] is the number of times the solver was at dl i (counting once after increasing dl and before decreasing dl)
     */
    vec<dl_c_t> dl_count;

    /**
     * @brief current unit watches
     * @note lineral_watches[lvl] contains all units added in dl lvl; used as stack
     */
    vec< list< lineral_watch > > lineral_watches;

    /**
     * @brief lazy-gauss-elim of XNF unit clauses, i.e., linerals
     */
    lin_sys_lazy_GE* lazy_gauss_jordan;

    /**
     * @brief current assignments of vars; assignments[i] contains lineral with LT i
     */
    vec< bool3 > alpha;
    var_t assigned_var_count = 0;
    
    /**
     * @brief phase of last assignment - phase saving
     */
    vec< bool3 > last_phase;

    /**
     * @brief dl of chosen/implied alpha assignments; i was true/false-decided at dl alpha_dl[i]
     */
    vec<var_t> alpha_dl;

    /**
     * @brief pointer to watchlist_elem where alpha[i] is assigned
     */
    vec<lin_w_it> alpha_lin;
    
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

    /**
     * @brief pointer implication graph representation of all 2-XNF clauses at dl 0
     */
    xornado::impl_graph IG;

    /**
     * @brief linerals that are derived on dl 0 AND are not yet propagated in IG
     */
    list<lineral> IG_linerals_to_be_propagated;
    
    var_t get_num_vars() const { return alpha.size()-1; };
    
    std::pair<var_t,cls_watch> analyze(const stats& s);
    std::pair<var_t,cls_watch> analyze_exp(const stats& s);
    std::pair<var_t,cls_watch> analyze_dpll(const stats& s);
    
    /**
     * @brief add new (learnt) clause to database
     * 
     * @param cls clause to be added; pointers must already be in correct shape (use init() and init_unit())
     * @param redundant bool to declare clause redundant or not; defaults to true
     * @return var_t idx of new clause; -1 if it was not added to clause database, i.e., cls was already a lineral
     */
    inline var_t add_learnt_cls(cls_watch&& cls, const bool& redundant = true) {
      const var_t i = add_cls_watch( std::move(cls), redundant, true );
      ++utility[i];
      return i;
    }

    inline void minimize(cls_watch_resolver& learnt_cls) {
      VERB(70, "   '------> " << learnt_cls.to_str() );

      //ensure each lvl has at most one element!
      learnt_cls.reduction(1, alpha_dl, alpha_trail_pos, dl_count);

      bool fix_ws = false;

      lin_sys L;
      auto it = learnt_cls.t_pos_to_idxs.begin();
      while(it!=learnt_cls.t_pos_to_idxs.end()) {
      //for(auto& [_, l] : learnt_cls.t_pos_to_idxs) {
        auto& [_,l] = *it;
        assert(l.size()==1);
        ////implementation true to original MiniSAT paper for clause minimization -- ineffective in practice..
        //var_t dl_ = learnt_cls.lineral_dl_count0[l.front()].first;
        //lineral_watch lin = lineral_watch(learnt_cls.linerals[l.front()], alpha, alpha_dl, dl_count, dl_);
        ////@todo optimize construction of clauses here?
        //list<lin_w_it> rs_lins;
        //vec<var_t> rs_clss_idxs;
        //for(const auto& i : lin.get_idxs_()) {
        //  rs_lins.push_back(alpha_lin[i]);
        //}
        //auto rs = get_reason(rs_lins, rs_clss_idxs);
        //assert(rs.get_unit()==lin.to_lineral());

        //const auto cls = get_reason(rs_lins, rs_clss_idxs).to_cls();
        //if( std::all_of(cls.get_ass_VS().get_linerals().begin(), cls.get_ass_VS().get_linerals().end(),
        //      [&L](const auto& lin){ return L.reduce(lin).is_zero(); })  ) {
        //  //remove lin!
        //  learnt_cls.linerals[l.front()].clear();
        //  --learnt_cls.num_nz_lins;
        //  l.clear();
        //}

        // write V_learnt_cls = L; then check for each l in L, if L \ {l}, xnf_clss |= l. In that case remove l from L.
        // for performance reasons, we check |= only on the implication graph, i.e., on the binary clauses
        // known as 'vivification' (?)
        const auto idx = l.front();

        for(var_t jdx = 0; jdx<learnt_cls.size(); ++jdx) {
          if(idx!=jdx) L.add_lineral( learnt_cls.linerals[jdx] );
        }

        lin_sys implied_lins = IG.implied_xlits( std::move(L) );
        L.clear();

        if( !implied_lins.is_consistent() || implied_lins.reduce( learnt_cls.linerals[idx] ).is_zero() ) {
          fix_ws = true;
          //remove idx!
          learnt_cls.linerals[idx].clear();
          --learnt_cls.num_nz_lins;
          l.clear();

          it = learnt_cls.t_pos_to_idxs.erase(it);
        } else {
          ++it;
        }
      }
      if(fix_ws) learnt_cls.fix_watched_idx(alpha_dl, alpha_trail_pos, dl_count);
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
        --assigned_var_count;
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
     * @brief construct reason cls by resolving list of clss; new clause is added to clss
     * 
     * @param rs_lins list of linerals whose reasons to resolve
     * @param rs_cls_idxs additional indices of clss to resolve with
     * @param max_size maximal size in each filtration level, (var_t) -1 for default heuristic
     * @return var_t indedx position of new cls_watch
     */
    inline cls_watch get_reason_and_init(const list<lin_w_it>& rs_lins, const vec<var_t> rs_cls_idxs, const var_t max_size = (var_t) -1) {
    #ifndef NDEBUG
      vec<lineral> lits; lits.reserve(lineral_watches.size());
      for(const auto& l_dl : lineral_watches) {
          for(const auto& l : l_dl) lits.emplace_back( l.to_lineral() );
      }
      lin_sys L_( std::move(lits) );

      lineral tmp;
    #endif
      //resolve cls to get true reason cls
      cls_watch_resolver r_cls;

      for(const auto& lin : rs_lins) {
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
          assert(r_cls.to_cls().reduced(alpha).is_unit());
          assert( !L_.is_consistent() || L_.reduce( r_cls.to_cls().reduced(alpha).get_unit()+tmp).is_constant() );
        }
      }
      //resolve with additional clause -- if required!
      for(const auto& idx : rs_cls_idxs) {
        const cls_watch& r_cls2 = xnf_clss[idx];
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
          assert(r_cls.to_cls().reduced(alpha).is_unit());
          assert( !L_.is_consistent() || L_.reduce( r_cls.to_cls().reduced(alpha).get_unit()+tmp).is_constant() );
        }
      }

      return r_cls.finalize(alpha_dl, alpha_trail_pos, dl_count, max_size);
    }

    /**
     * @brief construct reason cls by resolving list of clss; new clause is added to clss
     * @note same as 'get_reason_and_init()', but const!
     * 
     * @param rs_lins list of linerals whose reasons to resolve
     * @param rs_cls_idxs indices of clss to resolve
     * @param max_size maximal size in each filtration level, (var_t) -1 for default heuristic
     * @return var_t indedx position of new cls_watch
     */
    inline cls_watch get_reason(const list<lin_w_it>& rs_lins, const vec<var_t>& rs_cls_idxs, const var_t max_size = (var_t) -1) const {
    #ifdef DEBUG_SLOWER
      auto L_ = get_lineral_watches_lin_sys();
      lineral tmp;
    #endif
      //resolve cls to get true reason cls
      cls_watch_resolver r_cls;
      cls_watch r_cls2;
      for(const auto& lin : rs_lins) {
        if(lin->size()<=1) continue; //skip too short reason lins -- these are only guesses and implied alphas... they might only add new dependencies and can never reduce the max-alpha_trail_pos!
       #ifdef TREE_LIKE_REASON_CLS_COMP
        r_cls2 = get_reason(lin);
       #else
        r_cls2.operator=( std::move(cls_watch((lineral) *lin, alpha, alpha_dl, alpha_trail_pos, dl_count)) );
       #endif
        //resolve cls
        assert(r_cls2.is_unit(dl_count));
       #ifndef NDEBUG
        lineral unit = r_cls2.get_unit();
       #endif
        //extend r_cls2 with (unit of r_cls)+1, and r_cls with (unit of r_cls2)+1
        VERB(120, "c resolving clauses\nc   "<< BOLD(r_cls.to_str()) <<"\nc and\nc   "<< BOLD(r_cls2.to_str()));
       #ifdef TREE_LIKE_REASON_CLS_COMP
        r_cls.resolve( std::move(r_cls2), alpha, alpha_dl, alpha_trail_pos, dl_count);
       #else
        r_cls.resolve_unsafe( std::move(r_cls2), alpha, alpha_dl, alpha_trail_pos, dl_count);
       #endif
        VERB(120, "c and get \nc   "<< BOLD(r_cls.to_str()));
        VERB(120, "c");
        assert_slower( !L_.is_consistent() || L_.reduce(tmp+unit).is_zero() );
        assert(r_cls.to_cls().reduced(alpha).is_unit());
        assert_slower( !L_.is_consistent() || L_.reduce( r_cls.to_cls().reduced(alpha).get_unit()+tmp).is_constant() );
      }
      //resolve with additional clause -- if required!
      for(const var_t& idx : rs_cls_idxs) {
        const cls_watch& r_cls2 = xnf_clss[idx];
        //resolve cls
        assert(r_cls2.is_unit(dl_count));
        VERB(120, "c resolving clauses\nc   "<< BOLD(r_cls.to_str()) <<"\nc and\nc   "<< BOLD(r_cls2.to_str()));
       #ifdef TREE_LIKE_REASON_CLS_COMP
        r_cls.resolve( r_cls2, alpha, alpha_dl, alpha_trail_pos, dl_count);
       #else
        r_cls.resolve_unsafe(r_cls2, alpha, alpha_dl, alpha_trail_pos, dl_count);
       #endif
        VERB(120, "c and get \nc   "<< BOLD(r_cls.to_str()));
        VERB(120, "c");

        assert_slower( !L_.is_consistent() || L_.reduce(tmp+r_cls2.get_unit()).is_zero() );
        assert_slower( !L_.is_consistent() || L_.reduce( r_cls.to_cls().reduced(alpha).get_unit()+tmp).is_constant() );
      }

     #ifndef TREE_LIKE_REASON_CLS_COMP
      r_cls.fix_data_struct(alpha, alpha_dl, alpha_trail_pos, dl_count);
     #endif

      return r_cls.finalize(alpha_dl, alpha_trail_pos, dl_count, max_size);
    }

    inline cls_watch& get_reason_and_init(lin_w_it lin, var_t max_size = (var_t)-1) {
      VERB(120, "c constructing reason clause for "<<lin->to_str());

      //note, returning zero_cls might lead to complications!
      if(!lin->has_trivial_reason_cls() && lin->get_reason_lins().empty() && lin->get_reason_idxs().size()==1) return xnf_clss[lin->get_reason_idxs().front()];

    #ifndef TREE_LIKE_REASON_CLS_COMP
      //recursively rewrite lin to featrue all clss and only lins with trivial reason clss
      lin->simplify_reasons(true);
    #endif

      //construct reason clause
      const auto rs = lin->has_trivial_reason_cls() ? cls_watch( (lineral) *lin, alpha, alpha_dl, alpha_trail_pos, dl_count) : get_reason_and_init( lin->get_reason_lins(), lin->get_reason_idxs(), max_size);
      assert_slow(!rs.is_zero());

      //place rs into clss
      xnf_clss.emplace_back( std::move(rs) );
      utility.emplace_back( 0 );
      const var_t i = xnf_clss.size()-1;
      //set redundancy
      xnf_clss[i].set_redundancy(true);
      // add new cls to watch_lists
      if(xnf_clss.back().size()>0) watch_list[ (xnf_clss.back().get_wl0()) ].emplace_back(i);
      if(xnf_clss.back().size()>1) watch_list[ (xnf_clss.back().get_wl1()) ].emplace_back(i);
      //adapt reason of lin
      lin->clear_reason_idxs();
      lin->push_reason_idx( i );
      
      assert_slow(xnf_clss[i].is_unit(dl_count) && (xnf_clss[i].get_unit().reduced(alpha,equiv_lits)+lin->to_lineral().reduced(alpha,equiv_lits)).reduced(alpha,equiv_lits).is_zero());
      return xnf_clss[i];
    }

    inline cls_watch get_reason(lin_w_it lin, var_t max_size = (var_t)-1) {
      VERB(120, "c constructing reason clause for "<<lin->to_str());

      if(lin->has_trivial_reason_cls()) {
        return cls_watch( (lineral) *lin, alpha, alpha_dl, alpha_trail_pos, dl_count);
      }

    #ifndef TREE_LIKE_REASON_CLS_COMP
      //recursively rewrite lin to featrue all clss and only lins with trivial reason clss
      lin->simplify_reasons(true);
    #endif
    

      //construct reason clause
      const auto rs = get_reason( lin->get_reason_lins(), lin->get_reason_idxs(), max_size );
      
      assert(rs.is_unit(dl_count) && rs.get_unit().reduced(alpha)==lin->to_lineral().reduced(alpha));

      return rs;
    }
    
    inline cls_watch get_reason(const lin_w_it lin, var_t max_size = (var_t)-1) const {
      VERB(120, "c constructing reason clause for "<<lin->to_str());

      if(lin->has_trivial_reason_cls()) {
        return cls_watch( (lineral) *lin, alpha, alpha_dl, alpha_trail_pos, dl_count);
      }
      
    #ifndef TREE_LIKE_REASON_CLS_COMP
      //recursively rewrite lin to featrue all clss and only lins with trivial reason clss
      lin->simplify_reasons(true);
    #endif
    
      //construct reason clause
      const auto rs = get_reason( lin->get_reason_lins(), lin->get_reason_idxs(), max_size );
      
      //assert_slow(rs.is_unit(dl_count) && (rs.get_unit()+lin->to_lineral()).reduced(alpha).is_zero());
      assert(rs.is_unit(dl_count) && rs.get_unit().reduced(alpha)==lin->to_lineral().reduced(alpha));

      return rs;
    }
    
    inline cls_watch& get_reason_and_init(const trail_elem& t, var_t max_size = (var_t)-1) {
      return get_reason_and_init(t.lin, max_size);
    }
    
    inline cls_watch get_reason(const trail_elem& t, var_t max_size = (var_t)-1) const {
     #ifndef NDEBUG
      auto rs = get_reason(t.lin, max_size);
      assert( at_conflict() || rs.assert_data_struct(alpha, alpha_trail_pos, dl_count) );
      return rs;
     #else
      return get_reason(t.lin, max_size);
     #endif
    }
    
    //bumps utility recursively + recomputes LBD + sets clause as used in conflict
    inline void bump_reason(const stats& s, const lin_w_it lin) {
      for(const auto& i : lin->get_reason_idxs()) {
        ++utility[i];
        //recompute LBD - if redundant clause!
        if(!xnf_clss[i].is_irredundant()) {
          xnf_clss[i].set_used_in_conflict(s.no_confl);
          xnf_clss[i].recompute_LBD(alpha_dl);
          const auto new_tier = cls_idx_to_tier(i);
          promote_demote_cls(i, new_tier);
        }
      }
      for(const auto& l : lin->get_reason_lins()) {
        bump_reason(s, l);
      }
    }

    inline void promote_demote_cls(const var_t& i, const var_t& new_tier) {
      assert(new_tier<3);
      const auto& old_tier = tier[i];
      if(new_tier==old_tier) return;
      assert(!xnf_clss[i].is_irredundant());

      --tier_count[old_tier];
      ++tier_count[new_tier];
      tier[i] = new_tier;
    }

    typedef lineral (solver::*dec_heu_t)();
    typedef std::pair<var_t,cls_watch> (solver::*ca_t)(const stats&);

    double max_act_sc;
    double bump = 1;
    //according to 'Evaluating CDCL Variable Scoring Schemes' this should be between 1.01 and 1.2
    //smaller values for hard sat problems (like crypto) and larger useful with frequent restarts.
    //Lingeling used 1.2
    const double bump_start = 1.01;
    const double bump_end = 1.10;
    double bump_mult = bump_start; // 1/0.95 good for random instances

    void update_bump_mult(const stats& s) {
      if( 100000 < s.no_confl && s.no_confl<1000000) {
        const double linear_smoothing = ((double) s.no_confl-100000)/1000000;
        bump_mult = linear_smoothing * bump_end + (1-linear_smoothing) * bump_start; 
      }
    }

    void bump_score(const var_t& ind);
    void bump_score(const lineral& lit);
    void bump_score(const cls_watch& cls);
    void decay_score();
    

    void prefetch(var_t upd_lt) {
      //__builtin_prefetch( &L_watch_list[upd_lt] );
      //__builtin_prefetch( &watch_list[upd_lt] );
    }

    /**
     * @brief queue implied lineral for propagation (one-by-one); update data using propagate_implied_lineral
     * @note highest priority is conflict, followed by alpha and then equivs
     * 
     * @param lin lineral to be added to data structures
     * @param lvl dl-level on which lin should be propagated as 'type'
     * @param from_lineral_watch true iff lin originates from a lineral_watch, i.e., a clause did not just become a unit
     * @param type type of propagation (defaults to queue_t::NEW_UNIT)
     */
    inline void queue_implied_lineral(lin_w_it lin, const var_t lvl, const origin_t origin = origin_t::CLAUSE, const queue_t type = queue_t::NEW_UNIT) {
      assert(lin->assert_data_struct(alpha));
      if(type==queue_t::NEW_GUESS) {
        lineral_queue.q_alpha.emplace_front( lin, lvl, type, origin );
        prefetch( lin->get_assigning_ind() );
      } else if(lin->LT()==0) {
        lineral_queue.q_confl.emplace_front( lin, lvl, queue_t::IMPLIED_ALPHA, origin );
      } else if(origin==origin_t::LGJ || origin==origin_t::INIT || origin==origin_t::IG) {
        lineral_queue.q_lgj.emplace_back( lin, lvl, type, origin );
      } else if(lin->is_assigning(alpha)) {
        lineral_queue.q_alpha.emplace_back( lin, lvl, type, origin );
        prefetch( lin->get_assigning_ind() );
        //if(from_lineral_watch) lineral_queue.q_alpha.emplace_front( lin, lvl, type );
        //else                   lineral_queue.q_alpha.emplace_back( lin, lvl, type );
      } else if(lin->is_equiv()) {
        //TODO check if is_equiv() or is_equiv(alpha) performs better! -- the latter can increase the LBD of reason clause!
        lineral_queue.q_equiv.emplace_back( lin, lvl, type, origin );
        //if(from_lineral_watch) lineral_queue.q_equiv.emplace_front( lin, lvl, type );
        //else                   lineral_queue.q_equiv.emplace_back( lin, lvl, type );
      } else {
        lineral_queue.q_unit.emplace_back( lin, lvl, type, origin );
      }
    }

    /**
     * @brief propagates lineral from queue until a new alpha is propagated or the queue is empty
     * 
     * @return var_t idx of new lt; or -1 if no new alpha was propagated
     */
    inline var_t propagate_implied_lineral() {
      assert(!lineral_queue.empty());
      auto& [lin, lvl, type, origin] = lineral_queue.front();

      const var_t new_lt = process_lineral(lin, lvl, type, origin);
      
      lineral_queue.pop_front();
      return new_lt;
    }

    
    inline void add_new_lineral(lineral&& l, var_t lvl, queue_t type, origin_t origin) {
      lineral_watches[lvl].emplace_back( std::move(l), alpha, alpha_dl, dl_count, lvl );
      queue_implied_lineral( std::prev(lineral_watches[lvl].end()), lvl, origin, type);
    };
    
    inline void add_new_lineral(const lineral& l, var_t lvl, queue_t type, origin_t origin) {
      lineral_watches[lvl].emplace_back(l, alpha, alpha_dl, dl_count, lvl);
      queue_implied_lineral( std::prev(lineral_watches[lvl].end()), lvl, origin, type);
    };
    
    inline void add_new_guess(lineral&& l) {
      lineral_watches[dl].emplace_back( std::move(l), alpha, alpha_dl, dl_count, dl );
      queue_implied_lineral( std::prev(lineral_watches[dl].end()), dl, origin_t::GUESS, queue_t::NEW_GUESS);
    };

    /**
     * @brief decrease active_cls by one -- starting at dl lvl
     * 
     * @param idx of cls that became inactive
     */
    inline void decr_active_cls(const var_t& idx) {
      assert(!xnf_clss[idx].is_active(dl_count));
      if(!xnf_clss[idx].is_irredundant()) return;
      //update curr val
      assert(active_cls>0);
      --active_cls;
      //update vals in active_cls_stack
      for(var_t j = xnf_clss[idx].get_inactive_lvl(dl_count)+1; j<active_cls_stack.size(); ++j) {
        assert(active_cls_stack[j]>0);
        --active_cls_stack[j];
      }
     #if !defined(NDEBUG) && defined(DEBUG_SLOWER)
      //check if active_cls is updated to correct lvl!
      auto dl_count_cpy = dl_count;
      for(var_t lvl = dl; lvl>0; --lvl) {
          ++dl_count_cpy[lvl];
          cls reduced = xnf_clss[idx].to_cls().reduced(alpha,alpha_dl,lvl-1);
          if(xnf_clss[idx].get_inactive_lvl(dl_count)<lvl) {
            assert(!xnf_clss[idx].is_active(dl_count_cpy));
            assert(reduced.is_unit() || reduced.is_zero());
          } else {
            assert(xnf_clss[idx].is_active(dl_count_cpy));
            //NOTE: we do not know whether clss[idx] is actually zero; it might
            //      happen that an unwatched lineral is reduced to zero already on a lower dl!
            //      Thus we cannot assume !reduced.is_unit() and !reduced.is_zero() (!)
          }
      }
     #endif
    }

    /**
     * @brief adds new lineral to data structure if deduced at current dl; also reduces with current assignments to find new true/false assignments
     * 
     * @param lin iterator to lineral_watch in lineral_watches
     * @param lvl dl-level on which to propagate lin
     * @param type tral_t of lineral specifying type of propagation
     * @todo write seperate funcs for types: NEW_UNIT, IMPLIED_ALPHA and NEW_GUESS
     * 
     * @return var_t ind>=0 iff alpha[ind] is now assigned; ind==-1 means no new alpha-assignment
     */
    inline var_t process_lineral(lin_w_it lin, const var_t lvl, queue_t type, origin_t origin) {
      assert(lvl >= lin->get_lvl());
      assert(dl >= lvl);

      lineral_watch& l = *lin;

      if(origin == origin_t::LGJ) {
        l.init(alpha,alpha_dl,dl_count);
        assert((!l.is_active(alpha) && l.is_assigning(alpha)) || l.is_equiv());
      }

      VERB(65, "c " << std::to_string(lvl) << " : process_lineral " << type << origin << l.to_str() << " ~> " << l.to_lineral().reduced(alpha,equiv_lits).to_str() << (l.has_trivial_reason_cls() ? "" : (" with reason clause " + get_reason(lin, 1).to_str())) );
      if(l.is_reducible() && type!=queue_t::IMPLIED_ALPHA && origin!=origin_t::LGJ) {
        assert(lvl==l.get_lvl());
        assert_slow(lvl==0 || get_reason(lin).get_unit().reduced(alpha)==l.to_lineral().reduced(alpha));
        //reduce lin -- but only if type is NOT guess -- otherwise reason clause is not computed correctly!
        if(opt.eq && type!=queue_t::NEW_GUESS) l.reduce(alpha, alpha_dl, dl_count, equiv_lits, lvl);
        else                                   l.reduce(alpha, alpha_dl, dl_count, lvl);
        assert_slow(lvl==0 || l.is_zero() || get_reason(lin).get_unit().reduced(alpha)==l.to_lineral().reduced(alpha));
      }
      if(l.is_zero(alpha)) {
        //remove the lineral if it is actually just zero OR if it comes from LGJ -- then it just holds redundant info anyways
        if(l.is_zero() || origin==origin_t::LGJ) {
          lineral_watches[lvl].erase( lin );
        }
        return -1;
      }
      
      //TODO should we always reduce?! consider the following:
      //we already have UNIT x1+x2+x3 and now get x1; full reduction would give x2+x3, even though x1 would be assigning!
      //DO NOT REDUCE WITH TOO LONG XORs otherwise it might blow up!
      //@todo heuristically reduce less active variables; i.e. decrease number of 'inactive' vars and increase the active ones

      //add lineral for propagation to IG
      if(lvl==0 && opt.pp!=xornado_preproc::no && origin!=origin_t::IG && origin!=origin_t::LGJ) {
        //put lin in queue for propagation in IG -- if it is does not originate from IG
        IG_linerals_to_be_propagated.emplace_back( lin->to_lineral() );
      }

      //add to watch list if non-assigning AND not 'IMPLIED_ALPHA' (since this means it comes from a already watched lineral!)
      if(type!=queue_t::IMPLIED_ALPHA && !l.is_assigning()) {
        assert(l.size()>1);
        L_watch_list[ l.get_wl0() ].emplace_back( lvl, dl_count[lvl], lin );
        L_watch_list[ l.get_wl1() ].emplace_back( lvl, dl_count[lvl], lin );
        assert_slow( l.size()==0 || l.watches( l.get_wl0() ) || l.to_lineral().is_constant() );
        assert_slow( l.size()<=1 || l.watches( l.get_wl1() ) || l.to_lineral().is_constant() );
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
          l.set_reducibility(false);
          assert( l.get_equiv_lvl(alpha_dl) <= lvl );
          //add to trail
          trails[lvl].emplace_back( lt, trail_t::EQUIV, origin, lin );
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
            trails[lvl].emplace_back( l.LT(), trail_t::GUESS, origin, lin);
          }
        }

        //add lineral for propagation to LGJ
        if(lvl==0 && opt.lgj && origin!=origin_t::LGJ && origin!=origin_t::INIT) {
          //put lin in queue for propagation in IG -- if it is does not originate from LGJ (or INIT) - and is not assigning! (otherwise it will be added trough assign in GCP (!))
          linerals_to_be_added_to_LGJ.emplace_back( lin->to_lineral() );
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
      VERB(70, "c " << std::to_string(assigning_lvl) << " : new ALPHA " << l.get_assigning_lineral(alpha).to_str() << " from UNIT " << l.to_str() << (type!=queue_t::NEW_GUESS  && !l.has_trivial_reason_cls() && assigning_lvl>0 ? (" with reason clause " + get_reason(lin).to_str()) : "") );
      if(assigning_lvl < dl){
        VERB(70, "c " << std::to_string(assigning_lvl) << " : backtracking to " << std::to_string(assigning_lvl) << " as ALPHA was obtained on lower dl!" );
        backtrack(assigning_lvl);
        assert(dl==assigning_lvl);
        assert(opt.eq); //this can only happen when equivalence reductions are activated!
      }
      //get alpha-assignment
      const auto [lt2,val] = l.get_assignment(alpha);
      prefetch( lt2 );
      assert(l.is_assigning(alpha) && val!=bool3::None);
      trails[assigning_lvl].emplace_back( lt2, trail_t::ALPHA, origin, lin );
      l.set_reducibility(false);
      assert( alpha[lt2]==val || alpha[lt2]==bool3::None );
      alpha[lt2] = val;
      alpha_dl[lt2] = assigning_lvl;
      alpha_lin[lt2] = lin;
      ++assigned_var_count;
      assert(lt2==0 || alpha_dl[lt2] == std::max(l.get_assigning_lvl(alpha_dl), lvl));
      assert(alpha_trail_pos[lt2] == (var_t) -1);
      alpha_trail_pos[lt2] = stepwise_lit_trail_length;
      ++stepwise_lit_trail_length;
      assert(type==queue_t::NEW_GUESS || !l.is_reducible() || equiv_lits[lt2].ind==0 || alpha[equiv_lits[lt2].ind]!=bool3::None);
      //assert( !opt.lgj || origin!=origin_t::LGJ || lazy_gauss_jordan->check_cms_assignments(alpha) ); --skip this check: it sometimes fails and I do not know why :/ ...but we don't care about it as long as lazy_gauss_jordan->cms still propagates correctly! (and this is checked anyways as well!)
      return lt2;
    };

    /**
     * @brief triangulates watched linerals; i.e. updates them w.r.t. previous linerals and brings them in non-reduced row-echelon form
     * @note we cannot reuse the code from find_implications_by_GE or from check_lineral_watches_GE, since this function should be 'const'!
     */
    lin_sys get_lineral_watches_lin_sys() const;

    /**
     * @brief checks if lineral watches imply a conflict -- and if so  triangulates watched linerals; i.e. updates them w.r.t. previous linerals and brings them in non-reduced row-echelon form
     * 
     * @return L,cls where L is the lin_sys of all watched linerals and if L is inconsistent then cls is a conflict clause
     */
    std::tuple<lin_sys,cls_watch> check_lineral_watches_GE();


    /**
     * @brief adds a new cls to the database at dl 0
     * 
     * @param cls to be added
     * @param redundant bool to indicate whether the cls is redundant
     * @return var_t idx of new cls in vec<cls_watch> clss
     */
    inline var_t init_and_add_cls_watch(cls&& cls, const bool& redundant) {
      assert( dl == 0 );
      assert( !cls.is_zero() );
      cls_watch cls_w( std::move(cls) );
      cls_w.init(alpha, alpha_dl, alpha_trail_pos, dl_count);
      return add_cls_watch( std::move(cls_w), redundant, false );
    }

    /**
     * @brief adds a new cls to the database
     * 
     * @param cls to be added
     * @param redundant bool to indicate whether the cls is redundant
     * @return var_t idx of new cls in vec<cls_watch> clss
     */
    inline var_t add_cls_watch(cls_watch&& cls, const bool& redundant, const bool learnt_cls = false) {
      xnf_clss.emplace_back( std::move(cls) );
      utility.emplace_back( 0 );
      const var_t i = xnf_clss.size()-1;
      //set redundancy
      xnf_clss[i].set_redundancy(redundant);
      assert(redundant == !xnf_clss[i].is_irredundant());
      //update active_cls
      if(xnf_clss[i].is_irredundant()) {
        for(auto& a_cls : active_cls_stack) ++a_cls;
        ++active_cls;
      }
      //set tier for learnt cls
      if(learnt_cls) tier.emplace_back( cls_idx_to_tier(i) );
      else           tier.emplace_back( 0 );
      ++tier_count[tier.back()];
      //update cls
      VERB(90, "c adding new clause: " << BOLD(xnf_clss[i].to_str()) << "  --> gives with current assignments: "<<xnf_clss[i].to_cls().reduced(alpha).to_str());
      if(learnt_cls) VERB(90, "c XNF : " << xnf_clss[i].to_xnf_str());
      const auto ret = learnt_cls ? cls_upd_ret::UNIT : xnf_clss[i].init(alpha, alpha_dl, alpha_trail_pos, dl_count);
      //adapted from GCP
      switch (ret) {
      case cls_upd_ret::SAT:
          assert(!learnt_cls);
          assert(xnf_clss[i].is_sat(dl_count));
          assert(xnf_clss[i].is_inactive(dl_count));
          // IGNORE THIS CLAUSE FROM NOW ON
          decr_active_cls(i);
          break;
      case cls_upd_ret::UNIT: //includes UNSAT case (i.e. get_unit() reduces with assignments to 1 !)
      {
          assert(xnf_clss[i].is_unit(dl_count));
          assert(xnf_clss[i].is_inactive(dl_count));
          //update utility
          ++utility[i];
          // IGNORE THIS CLAUSE FROM NOW ON
          decr_active_cls(i);
          // NEW LIN-EQS
          //add on respective lvl!
          const var_t lvl = xnf_clss[i].get_unit_at_lvl();
          // @todo use add_new_lineral
          lineral_watches[lvl].emplace_back( std::move(xnf_clss[i].get_unit()), alpha, alpha_dl, dl_count, i, lvl);
          queue_implied_lineral( std::prev(lineral_watches[lvl].end()), lvl, (learnt_cls ? origin_t::CLAUSE : origin_t::INIT), queue_t::NEW_UNIT );
          break;
      }
      case cls_upd_ret::NONE:
          assert(!learnt_cls); //must not happen for learnt clauses
          assert(xnf_clss[i].is_none(dl_count));
          assert(xnf_clss[i].is_active(dl_count));
          break;
      }
      //clause only needs to be watched, if it has size()>1 (!)
      if(xnf_clss[i].size()>1) {
        watch_list[ (xnf_clss[i].get_wl0()) ].emplace_back(i);
        watch_list[ (xnf_clss[i].get_wl1()) ].emplace_back(i);
      }
      // add new cls to watch_lists
      assert( !xnf_clss[i].to_cls().is_zero() );
      assert( xnf_clss[i].assert_data_struct(alpha, alpha_trail_pos, dl_count) );
      return i;
    }

    vec<var_t> tier;
    var_t tier_count[3];
    var_t tier0_limit = 2;
    var_t tier1_limit = 7;

    var_t cls_idx_to_tier(const var_t i) {
      if(xnf_clss[i].is_irredundant()) return 0;
      const var_t lbd = xnf_clss[i].LBD(alpha_dl);
      if(lbd<=tier0_limit || xnf_clss[i].size()<=2) return 0;
      if(lbd<=tier1_limit) return 1;
      else return 2;
    };

    var_t tier_update_interval = 128;
    var_t last_tier_update = 0;
    bool need_update_tier_limits(stats& s) {
      //return false;
      if(s.no_confl < last_tier_update + tier_update_interval) return false;
      //update tier_update_interval
      last_tier_update = s.no_confl;
      if(tier_update_interval < 2<<16) tier_update_interval *= 2;
      return true;
    }

    vec<var_t> lbd_count;
    var_t max_lbd;
    double tier1_percentage = 0.2;
    double tier2_percentage = 0.5;

    void update_tier_limits() {
      //return;
      lbd_count.clear(); lbd_count.resize(get_num_vars()+1, 0);
      var_t ct = 0;
      for(var_t idx=0; idx<xnf_clss.size(); ++idx) {
        if(xnf_clss[idx].is_irredundant()) continue;
        if(xnf_clss[idx].last_used_in_conflict < last_tier_update) continue;
        const var_t lbd = xnf_clss[idx].LBD(alpha_dl);
        ++lbd_count[lbd];
        max_lbd = std::max(max_lbd, lbd);
        ++ct;
      }
      //add up 
      var_t sum = 0;
      var_t l = 0;
      while(sum < tier1_percentage * ct) {
        sum += lbd_count[l];
        ++l;
      }
      //tier0_limit = l-1;
      while(sum < tier2_percentage * ct) {
        sum += lbd_count[l];
        ++l;
      }
      tier1_limit = l-1;
      VERB(80, "c " << CYAN("update-tier-limits: tier0 " << std::to_string(tier_count[0]) << " tier1 " << std::to_string(tier_count[1]) << " tier2 " << std::to_string(tier_count[2]) ) );

      VERB(80, "c " << CYAN("new tier-limits: tier0: LBD <= " << std::to_string(tier0_limit) << " tier1: LBD <= " << std::to_string(tier1_limit)) );
      
      //re-tier all clauses!
      for(var_t idx=0; idx<xnf_clss.size(); ++idx) {
        const var_t new_tier = cls_idx_to_tier(idx);
        if(new_tier != tier[idx]) {
          promote_demote_cls(idx, new_tier);
        }
      }
      VERB(80, "c " << CYAN("update-tier-limits: tier0 " << std::to_string(tier_count[0]) << " tier1 " << std::to_string(tier_count[1]) << " tier2 " << std::to_string(tier_count[2]) ) );
    };

    var_t last_cleaning=0;
    /**
     * @brief clause database cleaning
     * @note may only be used in dl 0!
     */
    void clause_cleaning(stats& s);

    const unsigned int confl_until_restart_default = 2<<7; //number of conflicts between restarts
    unsigned int confl_until_restart = 0; //number of conflicts between restarts

    double forcing_fast = 0; //fast moving average of lbds of conflict clauses (short-term focus)
    double forcing_slow = 0; //slow moving average of lbds of conflict clauses (long-term focus)
    const unsigned int shift_fast = 5; //5 opt
    const double alpha_fast = (double) 1/(2<<shift_fast);
    const unsigned int shift_slow = 12;
    const double alpha_slow = (double) 1/(2<<shift_slow);
    double blocking = 0; //moving average of number of assigned vars
    const unsigned int shift_blocking = 11; //11 opt?
    double alpha_blocking = (double) 1/(2<<shift_blocking);

    double fast_slow_mult = 1.15; //opt 1.15?
    double blocking_mult_low = 1.4;
    double blocking_mult_high = 1.55;
    double blocking_mult = blocking_mult_low; //opt 1.6 better for block cipehrs? --> run more experiments!

    /**
     * @brief update exponential moving average scores for evaluating restarts
     * @note method and params based on paper 'Evaluating CDCL Restart Schemes' by A. Biere & A. Fröhlich
     * 
     * @param lbd new glue/lbd level
     * @param s current stats
     */
    void update_lbd_restart_vals(const var_t lbd, const stats& s) {
      if(s.no_confl<shift_fast) {
        const double alpha_fast_tmp = (double) 1/(2<<s.no_confl);
        forcing_fast = alpha_fast_tmp * lbd + (1-alpha_fast_tmp) * forcing_fast;
      } else {
        forcing_fast = alpha_fast * lbd + (1-alpha_fast) * forcing_fast;
      }
      if(s.no_confl<shift_slow) {
        const double alpha_slow_tmp = (double) 1/(2<<s.no_confl);
        forcing_slow = alpha_slow_tmp * lbd + (1-alpha_slow_tmp) * forcing_slow;
      } else {
        forcing_slow = alpha_slow * lbd + (1-alpha_slow) * forcing_slow;
      }
      if(s.no_confl<shift_blocking) {
        const double alpha_blocking_tmp = (double) 1/(2<<s.no_confl);
        blocking = alpha_blocking_tmp * assigned_var_count + (1-alpha_blocking_tmp) * blocking;
      } else {
        blocking = alpha_blocking * assigned_var_count + (1-alpha_blocking) * blocking;
      }

      if(50000 < s.no_confl && s.no_confl<=100000) {
        const double linear_smoothing = ((double) s.no_confl-50000)/50000;
        blocking_mult = linear_smoothing * blocking_mult_high + (1-linear_smoothing) * blocking_mult_low;
      }

      assert(forcing_fast>0 && forcing_slow>0);

      VERB(60, "c lbd: " << std::to_string(lbd) << " forcing_fast: " << forcing_fast << " forcing_slow: " << forcing_slow << " blocking: " << blocking);
    }


    /**
     * @brief checks if a restart is needed
     * @return true iff we should restart now
     */
    bool need_restart(stats& s) const;

    /**
     * @brief update params confl_unitl_restart according to restart heuristic; should be called after every call to restart()
     */
    void update_restart_schedule(const unsigned int& no_restarts);

    unsigned int confl_this_restart = 0; //number of conflicts since last restart
    /**
     * @brief restarts the solver; i.e. rm all assignments and backtracks to dl 0
     */
    void restart(stats& s);
    
  public:
    /**
     * @brief Construct main solver object
     * 
     * @param clss vector of lineral-vectors that represent the clauses
     * @param num_vars number of variables
     * @param opt_ options for heuristics, also includes number of vars
     */
    solver(const vec< vec<lineral> >& clss, const var_t num_vars, const options& opt_) noexcept;

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
    solver(const solver& o) noexcept : opt(o.opt), activity_score(o.activity_score), dl_count(o.dl_count), last_phase(o.last_phase), IG(o.IG) { 
    //solver(const solver& o) noexcept : opt(o.opt), activity_score(o.activity_score), dl_count(o.dl_count), last_phase(o.last_phase) { 
      opt.verb = 0;
      backtrack(0);
      // init data structures
      const auto num_vars = o.get_num_vars();
      //init watch_list
      watch_list.resize(num_vars+1);
      L_watch_list.resize(num_vars+1);
      lineral_watches = vec<list<lineral_watch>>(num_vars+1, list<lineral_watch>() );
    
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
      vec< cls > clss_; clss_.reserve(o.xnf_clss.size());
      for(const auto& cls : o.xnf_clss) clss_.emplace_back( std::move(cls.to_cls()) );
      init_clss( clss_ );
      
      for(var_t i = 1; i<=num_vars; ++i) {
          order_heap_vsids.insert( i );
      }

      //init restart params
      update_restart_schedule(0);

      assert(assert_data_structs());
    };

    ~solver() {
      if(opt.lgj) delete lazy_gauss_jordan;
    };

    /**
     * @brief init solver
     * 
     * @param clss vector of cls
     */
    void init_clss(const vec< cls >& clss) noexcept;


    /**
     * @brief checks whether solver is at conflict
     * 
     * @return true if current state is at conflict
     */
    inline bool at_conflict() const { return alpha[0]==bool3::True; };

    inline bool need_alpha_removal() {
      return dl==0 && !vars_to_be_removed.empty();
    }

    /**
     * @brief vars that can be removed (as they are assigned at dl 0)
     */
    vec<var_t> vars_to_be_removed;

    /**
     * @brief remove all fixed assignments on dl 0 from clauses
     * @note removing fixed assignments CANNOT deduce new linerals, hence output is always false!
     * @note the corresponding assignments must first be propagated + removes only those vars in vars_to_be_removed
     * 
     * @return true iff a new lineral was derived
     */
    bool remove_fixed_alpha();
    void remove_fixed_alpha(const var_t upd_lt);


    inline bool need_equiv_removal() {
      return dl==0 && remove_fixed_equiv_before_next_GCP;
    }
    
    bool remove_fixed_equiv_before_next_GCP = false;
    /**
     * @brief remove all literal equivalence on dl 0 from clauses 
     * 
     * @return true iff a new lineral was derived
     */
    bool remove_fixed_equiv();


    /**
     * @brief linerals that are derived on dl 0 AND are not yet propagated in IG
     */
    vec<lineral> linerals_to_be_added_to_LGJ;

    inline bool need_LGJ_update() {
      return opt.lgj && dl==0 && (!linerals_to_be_added_to_LGJ.empty() || !lazy_gauss_jordan->get_implied_literal_queue().empty());
    }

    inline bool find_implications_by_LGJ(stats& s) {
      const auto begin  = std::chrono::high_resolution_clock::now();
      assert( need_LGJ_update() );
      if(!lazy_gauss_jordan->get_implied_literal_queue().empty()) {
        VERB(80, "c " << RED("find_implications_by_LGJ: retrieving " << lazy_gauss_jordan->get_implied_literal_queue().size() << " new linerals") );
        fetch_LGJ_implications(s);
        const auto end  = std::chrono::high_resolution_clock::now();
        s.total_lgj_time += std::chrono::duration_cast<std::chrono::duration<double>>(end - begin);
      }
      if(linerals_to_be_added_to_LGJ.empty()) return true;
      assert(!linerals_to_be_added_to_LGJ.empty());

      VERB(80, "c " << RED("find_implications_by_LGJ: adding " << linerals_to_be_added_to_LGJ.size() << " new linerals to LGJ") );
      VERB(100, "c " << RED("adding: " << linerals_to_be_added_to_LGJ.size() << " new linerals to LGJ") );

      //add linerals to lazy_gauss_jordan
      var_t count = lazy_gauss_jordan->add_linerals( std::move(linerals_to_be_added_to_LGJ), alpha );
      if(count>0) {
        fetch_LGJ_implications(s);
      }
      linerals_to_be_added_to_LGJ.clear();

      VERB(80, "c " << GREEN("find_implications_by_LGJ: found " << count << " new assigning linerals") );

      const auto end  = std::chrono::high_resolution_clock::now();
      s.total_lgj_time += std::chrono::duration_cast<std::chrono::duration<double>>(end - begin);
      return count>0;
    }

    /**
     * @brief fetches latest linerals from LGJ module
     * 
     * @param s stats
     */
    void fetch_LGJ_implications(stats& s) {
      assert(opt.lgj);
      if(lazy_gauss_jordan->get_implied_literal_queue().empty()) return;
      list<lineral>& q = lazy_gauss_jordan->get_implied_literal_queue();
      for (auto&& lin : q) {
          ++s.no_lgj_prop;
          add_new_lineral( std::move(lin), dl, queue_t::NEW_UNIT, origin_t::LGJ );
          //While we KNOW that we have queue_t::IMPLIED_ALPHA, this implication might only be true under a sequence of assignments due to LGJ.
          //example: say x1, x2, x1+x2+x3 are returned by LGJ.
          //         Now if we call process_lineral(x1) and process_lineral(x2) we set alpha[1] and alpha[2].
          //         When process_linerals(x1+x2+x3) is called, it will lead to errors if queue_t::IMPLIED_ALPHA,
          //         since it requires l.get_assignment(alpha) to return x3.
          //         But when x1+x2+x3 is added to the queue, its watches are initiliazed (possibly) to x1, x2
          //         which are at this point NOT assigned at all.
      }
      lazy_gauss_jordan->clear_implied_literal_queue();
    }

    
    int ctr = 0;
    double avg_la_per_sec = 0;
    var_t checks_until_next_la = 1 << 7;
    long gauss_elim_schedule_wait = 1 << 7;
    /**
     * @brief decides whether a Gaußian Elimination in-processing step should be performed
     * 
     * @param stats s current stats
     */
    inline bool need_GE_inprocessing(stats& s) {
      if(at_conflict() || !lineral_queue.empty() || opt.gauss_elim_schedule==0) return false;
      else if(dl==0) return true; //always use gauss-jordan-elim on dl 0?
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
     * @return true iff a new forcing equivalence was found
     */
    bool find_implications_by_GE(stats& s);

    /**
     * @brief performs GCP; with basic in-processing on dl 0 (LGJ, IG, removal of fixed assignments and equivs) + GE on higher dl
     * @note inprocessing methods are chosen via the options of the solver.
     * 
     * @param s stats
     */
    void GCP_inprocess(stats &s) noexcept {
        do {
            if (s.cancelled.load()) {
                VERB(10, "c cancelled");
                return;
            }
            GCP(s);
        } while( !at_conflict() && 
            ( (need_GE_inprocessing(s) && find_implications_by_GE(s))
            || (need_IG_inprocessing(s) && find_implications_by_IG(s)) 
            || (need_LGJ_update()       && find_implications_by_LGJ(s))
            //|| (need_alpha_removal()    && remove_fixed_alpha()) //moved into GCP!
            //|| (need_equiv_removal()    && remove_fixed_equiv()) //moved into GCP!
            ) );
        //NOTE: LGJ update must be BEFORE removing fixed equivs, as new equivs first need to be added
        //      before they are 'removed' -- otherwise LGJ might become inconsistent with latest props...
    }

    
    /**
     * @brief performs GCP
     * 
     * @param s stats
     */
    void GCP(stats& s) noexcept;

    /**
     * @brief performs linear algebra in-processing;
     * @note only call this on dl 0!
     * 
     * @param s stats
     * @return bool true iff new clauses were added, and new alpha assignments derived
     */
    bool initial_GE_processing(stats& s) {
      assert(dl==0);
      if( !need_GE_inprocessing(s) ) return false;
      return find_implications_by_GE(s);
    };

    /**
     * @brief decide whether solver should perform xornado in/preprocessing
     */
    bool need_IG_inprocessing(stats& s) {
      return dl==0 && opt.pp!=xornado_preproc::no && (IG_linerals_to_be_propagated.size()>0 || s.no_ig==0);
    }

    /**
     * @brief run xornado preprocessing on current state
     * @note currently only works in dl 0, and only when opts.xornado is set
     * 
     */
    bool find_implications_by_IG(stats& s) {
      assert(dl==0);
      if(s.no_ig>100 && opt.pp==xornado_preproc::scc_fls) {
        IG.get_opts()->pp = xornado::preproc::scc;
        opt.pp = xornado_preproc::scc;
      }
      ++s.no_ig;
      const auto begin  = std::chrono::high_resolution_clock::now();
      VERB(50, "c implication graph in-processing -- propagating " << IG_linerals_to_be_propagated.size() << " new linerals.");
      if(IG_linerals_to_be_propagated.size()>0) {
        lin_sys sys( std::move(IG_linerals_to_be_propagated) );
        IG.add_new_xsys( std::move(sys) );
      }
      IG_linerals_to_be_propagated.clear();

      const auto IG_linsys_begin = std::prev( IG.get_xsys_stack().back().end() );
      //call xornado-preprocessing
      IG.preprocess();
      //add new linerals
      var_t count = 0;
      for(auto it = std::next(IG_linsys_begin); it!=IG.get_xsys_stack().back().end(); ++it) {
        for(auto it2 = it->get_linerals().begin(); it2 != it->get_linerals().end(); ++it2) {
          const auto& l = *it2;
          add_new_lineral(l, 0, queue_t::NEW_UNIT, origin_t::IG);
          ++count;
          if(!l.is_zero()) ++s.no_ig_prop;
        }
      }
      VERB(50, "c Xornado in-processing deduced " << count << " new linerals");
      
      const auto end  = std::chrono::high_resolution_clock::now();
      s.total_ig_time += std::chrono::duration_cast<std::chrono::duration<double>>(end - begin);
      return count>0;
    }

    /**
     * @brief backtracks to dl
     */
    void backtrack(const var_t& lvl);


    //decision heuristics
    /**
     * @brief branch on first vertex (i.e. vert at first position in L)
     */
    lineral dh_vsids();

    /**
     * @brief branch on ind that has the shortest watch_list
     */
    lineral dh_shortest_wl();

    /**
     * @brief branch on ind that has the longest watch_list
     */
    lineral dh_longest_wl();

    /**
     * @brief branch on x[i] where i smallest ind not yet guessed!
     */
    lineral dh_lex_LT();
    
    /**
     * @brief wrapper for dec_heu_t funcs to first guess according to guessing path
     * @note dh_gp<dh> also has type dec_heu_t
     */
    template<const dec_heu_t dh>
    lineral dh_gp();

    //solve-main
    void solve(stats& s); //{ opt.ca = ca_alg::dpll; return cdcl_solve(s); };
    stats solve() { stats s; solve(s); return s; };
    
    void dpll_solve(stats& s);
    stats dpll_solve() { stats s; dpll_solve(s); return s; };

    //find all solutions of lin_sys
    void solve_L(const lin_sys& L, stats& s) const;

    var_t get_dl() const noexcept { return dl; };
    
    options* get_opts() { return &opt; };
    const options* get_const_opts() const { return &opt; };

    std::string to_str() const noexcept;
    std::string to_xnf_str() const noexcept;

    solver& operator=(const solver& ig) = default;

    bool assert_data_structs() const noexcept;
    void print_trail(std::string lead = "") const noexcept;

};