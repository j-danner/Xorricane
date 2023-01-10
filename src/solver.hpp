#pragma once

//STILL BUGGY -DO NOT USE-
//#define USE_LT_IDXS

#include <stack>
#include <math.h>
#include <map>
#include <list>
#include <queue>
#include <memory>

#include "solve.hpp"
#include "misc.hpp"
#include "xlit/xlit.hpp"
#include "xlit/xsys.hpp"
#include "xlit/xcls_watch.hpp"
#include "xlit/xcls.hpp"

struct state_repr {
  /**
   * @brief number of active clauses
   */
  var_t active_cls;

  /**
   * @brief current non-constant assignments
   */
  xsys L;
  
  state_repr(const var_t _active_cls, const xsys& _L) : active_cls(_active_cls), L(_L) {};
};

class solver
{
  private:
    /**
     * @brief xor-clause watchers
     */
    vec< xcls_watch > xclss;

   #ifndef NDEBUG
    /**
     * @brief stack of lists of xsyses for backtracking
     */
    std::deque< std::list<xsys> > xsys_stack;
   #endif

    /**
     * @brief watch_list; watch_list[i] contains all idxs j s.t. xclss[j] watches indet i
     */
    vec< std::list<var_t> > watch_list;

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
    std::list<state_repr> state_stack;
    
    /**
     * @brief 'activity' of each variable; used for decision heuristic
     * @note entries must be strictly positive! (otherwise max_path/max_tree might fail!)
     */
    vec<unsigned int> activity_score;
    unsigned int bump = 1;
    float decay = 0.9;

    bool is_consistent = true;

    //CDCL vars
    /**
     * @brief counts how often a dl was visited -- required to quickly discard xlit that were already watched previously in the current search tree
     *        dl_count[i] is the number of times the solver was at dl i (counting once after increasing dl and before decreasing dl)
     */
    vec<var_t> dl_count;

    /**
     * @brief current assignments of vars; assignments[i] contains xlit with LT i
     */
    vec< xlit > assignments;
    
    /**
     * @brief current assignments of vars; assignments[i] contains xlit with LT i
     */
    vec< bool3 > alpha;

    /**
     * @brief dl of chosen assignments; i was assigned at dl assignments_dl[i]
     */
    vec<var_t> assignments_dl;

    /**
     * @brief idx of reason clause of propagated units
     */
    vec<var_t> reason;

    /**
     * @brief trail of assignments/unit-propagations
     */
    vec<var_t> trail;

    /**
     * @brief queue of lits that were assigned but not yet propagated
     * @note lits first need to be put into gcp_queue before being added to the trail!
     */
    std::queue<var_t> gcp_queue;

    xcls get_last_reason() const;

    std::pair<var_t,xcls> analyze();
    std::pair<var_t,xcls> analyze_exp();
    std::pair<var_t,xcls> analyze_no_sres();
    std::pair<var_t,xcls> analyze_dpll();

    void add_learnt_cls(xcls&& cls);

    bool pop_trail();

    typedef std::pair<xsys,xsys> (solver::*dec_heu_t)() const;
    typedef std::pair<var_t,xcls> (solver::*ca_t)();

    void GCP(stats& s);

    void bump_score(const xsys& new_xsys);
    void bump_score(const xlit& lit);
    void decay_score();

    inline void add_new_xsys(const xsys& L) {
     #ifndef NDEBUG
      xsys_stack.back().push_back(L);
     #endif
      //update assignments
      for(const auto& [lt,idx] : L.get_pivot_poly_idx()) {
        assignments[lt] = L.get_xlits(idx);
        assignments_dl[lt] = dl;
        trail.emplace_back( lt );
        //comes from guess
        reason.emplace_back( -1 );
        //update alpha
        alpha[lt] = assignments[lt].as_bool3();
        //put into gcp_queue if necessary!
        if(alpha[lt] != bool3::None) gcp_queue.emplace(lt);
      };
      is_consistent &= L.is_consistent();
    };

    void add_new_xlit(const xlit& lit) {
      const var_t lt = lit.LT();
      //update assignments
      assignments[lt] = lit;
      assignments_dl[lt] = dl;
      if(lit.is_one()) is_consistent = false;
      alpha[lt] = assignments[lt].as_bool3();
      //put into gcp_queue if necessary!
      if(alpha[lt] != bool3::None) gcp_queue.emplace(lt);

      //TODO search for new uniquely determined inds!

    };

    void init_and_add_xcls_watch(xcls&& cls) {
      xclss.emplace_back( std::move(cls) );
      // update watch_lists and init iterators of watch_lits!
      const var_t i = xclss.size()-1;
      watch_list[ *(xclss.back().get_lw0()) ].emplace_back(i);
      xclss.back().set_wl_it0( std::next( watch_list[ *(xclss.back().get_lw0()) ].end(), -1) ); //add iterator to last el in watch_list
      watch_list[ *(xclss.back().get_lw1()) ].emplace_back(i);
      xclss.back().set_wl_it1( std::next( watch_list[ *(xclss.back().get_lw1()) ].end(), -1) ); //add iterator to last el in watch_list
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
    solver(const solver& o) noexcept : xclss(o.xclss), opt(o.opt), dl(o.dl), active_cls(o.active_cls), activity_score(o.activity_score) {
     #ifndef NDEBUG
      xsys_stack = o.xsys_stack;
     #endif
    };

    ~solver() = default;
    
    /**
     * @brief saves current state to state_stack
     */
    void save_state();

    /**
     * @brief backtracks to dl
     */
    void backtrack();


    //decision heuristics
    /*
     * @brief branch on first vertex (i.e. vert at first position in L)
     */
    std::pair< xsys, xsys > dh_first_vert() const;
    /*
     * @brief branch on LT of first vertex (i.e. vert at first position in L)
     */
    std::pair< xsys, xsys > dh_first_LT() const;
    /*
     * @brief branch on x[i] where i smallest ind not yet guessed!
     */
    std::pair< xsys, xsys > dh_lex_LT() const;

    //solve-main
    void dpll_solve(stats& s);
    stats dpll_solve() { stats s; dpll_solve(s); return s; };

    var_t get_dl() const noexcept { return dl; };
    
    options* get_opts() { return &opt; };

    std::string to_str() const noexcept;

    solver& operator=(const solver& ig) = delete;

    bool assert_data_structs() const noexcept;
    void print_assignments(std::string lead = "") const noexcept;
    void print_trail(std::string lead = "") const noexcept;

};