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
#define GCP_QUEUE gcp_queues.back()
#define ASSIGNMENT_WATCH assignment_watches.back()

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

enum class trail_t { NEW_UNIT, IMPLIED_ALPHA };

struct trail_elem {
  var_t ind;
  trail_t type;

  trail_elem() : ind(0), type(trail_t::NEW_UNIT) {};
  trail_elem(const var_t _ind, const trail_t _type) : ind(_ind), type(_type) {};
  trail_elem(const trail_elem& other) : ind(other.ind), type(other.type) {};
  trail_elem(trail_elem&& other) : ind(other.ind), type(other.type) {};
};

class solver
{
  private:
    /**
     * @brief xor-clause watchers
     */
    vec< xcls_watch > xclss;

    /**
     * @brief watch_list[i] contains all idxs j s.t. xclss[j] watches indet i
     */
    vec< std::list<var_t> > watch_list;
    
    /**
     * @brief watch_list[i] contains all idxs j s.t. xlits[j] watches indet i
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
     * @brief number of active unit xcls
     */
    var_t active_lits;

    /**
     * @brief stack of state repr -- used for backtracking (and for dl-wise update of learnt-clauses)
     */
    vec<state_repr> state_stack;
    
    /**
     * @brief 'activity' of each variable; used for decision heuristic
     * @note entries must be strictly positive! (otherwise max_path/max_tree might fail!)
     */
    vec<unsigned int> activity_score;
    unsigned int bump = 1;
    float decay = 0.9;

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
    vec<var_t> dl_count;

#ifdef EXACT_UNIT_TRACKING
    /**
     * @brief current assignments of vars; assignments[i] contains xlit with LT i
     */
    vec< xlit > assignments;
#endif
    
    /**
     * @brief current assignments of vars; stored as xlit_watches
     * @note assignments_watches[lvl] contains all units added in dl lvl; used as stack
     */
    vec< vec< xlit_watch > > assignments_watches;
    //TODO change to vec< std::list< xlit_watch> > assignments_watches; (!)
    //should allow us to access contents more quickly!

    /**
     * @brief assignments_list[lt] contains all assignments with leading term lt
     */
    vec< std::list< std::array<var_t,4> > > assignments_list;

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


#ifdef EXACT_UNIT_TRACKING
    /**
     * @brief dl of chosen assignments; i was assigned at dl assignments_dl[i]
     */
    vec<var_t> assignments_dl;
#endif

    /**
     * @brief if equiv_lits[i] is non-zero, i is congruent to equiv_lits[i] or equiv_lits[i]+1 (can be checked using assignments[i]!)
     */
    vec<var_t> equiv_lits;

    /**
     * @brief idx of reason clause of propagated units
     */
    vec<var_t> reason_ALPHA;
    //assert(false);
    // i guess we need to track reason clauses in two ways: reason cls for UNITS AND reason cls for ALPHA..... CDCL needs to know the reason for every ALPHA, and reduce with it, but to know the reason clauses for ALPHA, we need to know the reason clause for the corresponding UNIT; i.e. for every UNITs we need to access the corr reasons, which are then put into the ALPHA-reasons
    //related: should the trail only manage the ALPHA-assignments?, i.e., which are assignments are we actually learning on?! (i guess only ALPHA-assignments suffice...)

    /**
     * @brief trail of decisions/unit-propagations
     * @note trail[lvl] is the trail at level lvl
     */
    vec< std::list<trail_elem> > trails;

    /**
     * @brief queue of lits that were assigned but not yet propagated to clauses
     */
    vec< std::queue<var_t> > gcp_queues;
    
    xcls get_last_reason() const;

    std::pair<var_t,xcls> analyze();
    std::pair<var_t,xcls> analyze_exp();
    std::pair<var_t,xcls> analyze_no_sres();
    std::pair<var_t,xcls> analyze_dpll();

    void add_learnt_cls(xcls&& cls);

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
        assignments_dl[TRAIL.back().ind] = 0;
        reason_ALPHA[TRAIL.back().ind] = 0;
      }
#endif
      //store last_phase
      save_phase();
      alpha[TRAIL.back().ind] = bool3::None;
      alpha_dl[TRAIL.back().ind] = 0;
      TRAIL.pop_back();
      return true;
    }


    typedef std::pair<xsys,xsys> (solver::*dec_heu_t)() const;
    typedef std::pair<var_t,xcls> (solver::*ca_t)();

    void GCP(stats& s);

    void bump_score(const xsys& new_xsys);
    void bump_score(const xlit& lit);
    void decay_score();

    inline void add_new_guess(const xsys& L) {
      //update assignments
      for(const auto& [lt,idx] : L.get_pivot_poly_idx()) {
        add_new_xlit(*idx, -1, dl);
        //OLD CODE
        //assert(assignments[lt].is_zero()); //ensure that guess is actually new!
        ////TODO should we allow to guess variables for which we already have information?
        //assignments[lt] = L.get_xlits(idx);
        //assignments_dl[lt] = dl;
        //trail.emplace_back( lt );
        ////comes from guess
        //reason_UNIT.emplace_back( -1 );
        ////update alpha
        //alpha[lt] = assignments[lt].as_bool3();
        ////put into gcp_queue if necessary!
        //if(alpha[lt] != bool3::None) {
        //  gcp_queue.emplace(lt);
        //  alpha_dl[lt] = dl;
        //}
      };
    };

    /**
     * @brief decrease active_cls by one -- starting at dl lvl
     * 
     * @param lvl dl in which cls got inactive
     */
    inline void decr_active_cls(const var_t& lvl) {
      //update curr val
      --active_cls;
      //update vals in state_stack
      for(var_t j = lvl+1; j<state_stack.size(); ++j) --state_stack[j].active_cls;
    }
    
    /**
     * @brief decrease active_cls by one -- starting at dl lvl
     * 
     * @param lvl dl in which cls got inactive
     */
    inline void incr_active_cls(const var_t& lvl) {
      //update curr val
      ++active_cls;
      //update vals in state_stack
      for(var_t j = lvl+1; j<state_stack.size(); ++j) ++state_stack[j].active_cls;
    }

    xlit _reduced_lit;
    /**
     * @brief adds new xlit to data structure if deduced at current dl; also reduces with current assignments to find new true/false assignments
     * 
     * @param lit literal to be added
     * @param rs idx of reason_UNIT clause
     * @param lvl dl in which lit is deduced
     * 
     * @return bool true iff xlit was actually new at current dl!
     */
    inline bool add_new_xlit(const xlit& lit, const var_t& rs, const var_t& lvl) {
      //new code
      //store lit in 
      _reduced_lit = lit;
      _reduced_lit.reduce(alpha); //reduce with alpha assignments -- the least we should do!
      //TODO optimize non-debuging code!
#ifdef EXACT_UNIT_TRACKING
      if( !_reduced_lit.is_assigning() ) _reduced_lit.reduce(assignments, assignments_dl, lvl); //reduce with assignments AND alpha...
#endif
      if(_reduced_lit.is_zero()) return false; 
      if(lvl < dl) {
        assert(false); //due to arc-consistency, we should never add a literal on a previous dl!
        VERB(100, "adding UNIT on previous level!");
      }
      VERB(65, "c " + std::to_string(lvl) + " : new UNIT " + lit.to_str() + " ~> " + _reduced_lit.to_str() + ( 0<=rs && rs<xclss.size() ? " with reason clause " + xclss[rs].to_str() : "") );
      
      const var_t lt = _reduced_lit.LT();
      //TODO should we always reduce?! consider the following:
      //we already have UNIT x1+x2+x3 and now get x1; as of now, we add x2+x3, even though x1 would be assigning!
      //DO NOT REDUCE WITH TOO LONG XORs otherwise it might blow up!
      // add to trail //TODO add in propoer position in trail!
      trails[lvl].emplace_back(lt, trail_t::NEW_UNIT);

#ifdef EXACT_UNIT_TRACKING
      // update assignments
      if(assignments[lt].is_zero()) {
        assignments[lt] = _reduced_lit;
        assignments_dl[lt] = lvl;
      }
      //assignments_xsys.add_reduced_lit(assignments[lt]); //might fail if lvl < dl (!)
      //add _reduced_lit to assignments_xsys
      assert((var_t)state_stack.size() >= dl);
      for(auto i = lvl+1; i < (var_t) state_stack.size(); ++i) {
        state_stack[i].L += xsys(_reduced_lit);
      }
      assignments_xsys += xsys(_reduced_lit);
#endif

      //assert( assignments_watch.back().to_xlit().is_zero() );
      assignments_watches[lvl].emplace_back( std::move(_reduced_lit), alpha, alpha_dl, lvl, dl_count, rs );
      assert( assignments_watches[lvl].back().is_active(dl_count) );
      // add to L_watch_list's -- if there is anything to watch
      if(assignments_watches[lvl].back().size()>0) {
        L_watch_list[ assignments_watches[lvl].back().get_wl0() ].emplace_back( std::array<var_t,4>({lvl, (var_t) (assignments_watches[lvl].size()-1), lvl, dl_count[lvl]}) );
        if(assignments_watches[lvl].back().get_wl0() != assignments_watches[lvl].back().get_wl1()) L_watch_list[ assignments_watches[lvl].back().get_wl1() ].emplace_back( std::array<var_t,4>({lvl, (var_t) (assignments_watches[lvl].size()-1), lvl, dl_count[lvl]}) );
      }
      assignments_list[lt].emplace_back( std::array<var_t,4>({lvl, (var_t) (assignments_watches[lvl].size()-1), lvl, dl_count[lvl]}) );

      //if assignments_watch.back() is already assigned, update alpha!
      const auto [lt2,val] = assignments_watches[lvl].back().get_assignment(alpha);
      if(val!=bool3::None) {
        if(lvl < dl && alpha[lt2]!=bool3::None && alpha_dl[lt2] > lvl) {
          assert(false);
          //TODO what if val is now determined on lvl < dl; where alpha_dl[lt2] > lvl; we should replace alpha_dl[lt2] AND reason_ALPHA[lt2]; however then we need to be careful when dealing with the trail in trails[ alpha_dl[lt2] ]], as lt2 must be skipped... also this new ALPHA-assignment might have implied other assignments at lvl, how to proceed with those??
          //maybe add upd_queue for every dl?
          //merge upd_queue and gcp_queue and integrate find_implied_alpha() into GCP() ?
        }
        assert( alpha[lt2]==val || alpha[lt2]==bool3::None );
        alpha[lt2] = val;
        alpha_dl[lt2] = assignments_watches[lvl].back().get_assigning_lvl(alpha_dl);
        reason_ALPHA[lt2] = rs;
        VERB(70, "c "+ std::to_string(alpha_dl[lt2]) + " : new ALPHA " + assignments_watches[lvl].back().get_assigning_xlit(alpha).to_str() + " from UNIT " + assignments_watches[lvl].back().to_str() + ( (reason_ALPHA[lt2]<xclss.size()) ? " with reason clause " + xclss[reason_ALPHA[lt2]].to_str() : "") );
        GCP_QUEUE.emplace(lt2); //ensure it is propagated now!
        if(alpha_dl[lt2] < dl) {
          gcp_queues[lvl].emplace(lt2); //ensure it is propagated after backtracking!
        }
        if(lt!=lt2) {
          trails[ alpha_dl[lt2] ].emplace_back( lt2, trail_t::IMPLIED_ALPHA );
        }
        if (lt2==0) { assert(!no_conflict()); return true; };
#ifdef EXACT_UNIT_TRACKING
        if(lt!=lt2) {
          //update assignments
          assert( assignments[lt2].is_zero() || assignments_dl[lt2] == alpha_dl[lt2] );
          //either lt2 has not been assigned yet; or it has been done on this level; i.e., we can just overwrite it! (note: here we have a forcing assignment, i.e., a better assignment...)
          //trails[ alpha_dl[lt2] ].emplace_back( lt2, trail_t::IMPLIED_ALPHA );
          assignments[lt2] = assignments_watches[lvl].back().get_assigning_xlit(alpha);
          assignments_dl[lt2] = alpha_dl[lt2];
        }
#endif
      }
      //else if (assignments_watch.back().is_equiv()) { //TODO update to check is_equiv for xlit_watches!!
      //  equiv_lits[lt] = assignments[lt].get_idxs_()[1];
      //  VERB(65, "c " + std::to_string(lvl) + ": new EQUIV " + assignments[lt].to_str() )
      //  //TODO currently unused information!
      //}
      
      return true;
    };

    /**
     * @brief triangulates watched linerals; i.e. updates them w.r.t. previous linearls and brings them in non-reduced row-echelon form
     */
    inline xsys get_assignments_xsys() {
      vec<xlit> lits; lits.reserve(assignments_watches.size());
      for(const auto& l_dl : assignments_watches) {
          for(const auto& l : l_dl) if(l.is_active(dl_count)) lits.emplace_back( l.to_xlit() );
      }
      return xsys( std::move(lits) );

      //triangulate code snippet -- NOT WORKING!
//
//      //we need to rewrite the current history, i.e., trails, alpha, alpha_dl, reason_ALPHA, assignments, assignments_dl, assignments_list, assignments_watches and L_watch_list -- as if we reduced every new unit directly with the previous units!
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
//          xlit& lit = assignments_watches[lvl][i];
//          //reduce
//          while( !assignments_list_new[lit.LT()].empty() ) {
//            const auto& [lvl2, i2, dl2, dl_c2] = assignments_list_new[lit.LT()].back();
//            assert( dl_count[dl2] == dl_c2 );
//            lit += assignments_watches[lvl2][i2];
//          }
//          if(lit.is_zero()) continue;
//          //re-initialize lit
//          assignments_watches[lvl][i].init(alpha, alpha_dl);
//          //add to L_watch_list and assignments_list_new
//          assignments_list_new[lit.LT()].emplace_back( std::array<var_t,4>({_, i, dl_, dl_c}) );
//          L_watch_list[ assignments_watches[lvl].back().get_wl0() ].emplace_back( std::array<var_t,4>({_, i, dl_, dl_c}) );
//          if(assignments_watches[lvl].back().get_wl0() != assignments_watches[lvl].back().get_wl1()) L_watch_list[ assignments_watches[lvl].back().get_wl1() ].emplace_back( std::array<var_t,4>({_, i, dl_, dl_c}) );
//        }
//      }
//      //replace assignments_list by assignments_list_new
//      assignments_list = std::move(assignments_list_new);
//
//      VERB(65, "c triangulate end" )
    }

    inline void init_and_add_xcls_watch(xcls&& cls) {
      xclss.emplace_back( std::move(cls) );
      // update watch_lists and init iterators of watch_lits!
      const var_t i = xclss.size()-1;
      watch_list[ (xclss.back().get_wl0()) ].emplace_back(i);
      watch_list[ (xclss.back().get_wl1()) ].emplace_back(i);
      assert(assert_data_structs());
    }

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
    solver(const solver& o) noexcept : xclss(o.xclss), opt(o.opt), dl(o.dl), active_cls(o.active_cls), activity_score(o.activity_score) {};

    ~solver() = default;
    
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
    void dpll_solve(stats& s);
    stats dpll_solve() { stats s; dpll_solve(s); return s; };
    
    void cdcl_solve(stats& s);
    stats cdcl_solve() { stats s; cdcl_solve(s); return s; };

    var_t get_dl() const noexcept { return dl; };
    
    options* get_opts() { return &opt; };

    std::string to_str() const noexcept;

    solver& operator=(const solver& ig) = delete;

    bool assert_data_structs() const noexcept;
    void print_assignments(std::string lead = "") const noexcept;
    void print_trail(std::string lead = "") const noexcept;

};