#pragma once
//std
#include <atomic>
#include <stdint.h>
#include <cassert>
#include <chrono>
#include <vector>
#include <list>
#include <iostream>
#include <iomanip>
#include <string>
#include <unordered_map>
#include <set>
#include <deque>
//other

#include <boost/container/vector.hpp>
#include <boost/container/stable_vector.hpp>
#include <boost/container/allocator.hpp>
#include <boost/container/adaptive_pool.hpp>
#define BOOST_POOL_NO_MT //disable multithreading support
#include <boost/pool/pool_alloc.hpp>


#include "rang/rang.hpp"

//activate additional debugging assertions
//#define DEBUG_SLOW
//#define DEBUG_SLOWER
#ifdef NDEBUG
  #undef DEBUG_SLOW
  #undef DEBUG_SLOWER
#endif
#ifdef DEBUG_SLOWER
  #define DEBUG_SLOW
#endif

#if defined(DEBUG_SLOW) && !defined(NDEBUG)
  #define assert_slow(expr) assert(expr)
#else
  #define assert_slow(expr) {}
#endif

#if defined(DEBUG_SLOWER) && !defined(NDEBUG)
  #define assert_slower(expr) assert(expr)
#else
  #define assert_slower(expr) {}
#endif

//verbosity output
#ifdef VERBOSITY
  #define VERB(lvl, msg) if(this->opt.verb >= lvl) { std::cout << msg << std::endl; }
#else
  #define VERB(lvl, msg)
#endif

#define BOLD(str) rang::style::bold << str << rang::style::reset
#define ITALIC(str) rang::style::italic << str << rang::style::reset
#define DIM(str) rang::style::dim << str << rang::style::reset
#define UNDERLINE(str) rang::style::underline << str << rang::style::reset

#define GRAY(str) rang::fg::gray<< str << rang::style::reset
#define RED(str) rang::fg::red<< str << rang::style::reset
#define GREEN(str) rang::fg::green<< str << rang::style::reset
#define YELLOW(str) rang::fg::yellow<< str << rang::style::reset
#define BLUE(str) rang::fg::blue<< str << rang::style::reset
#define MAGENTA(str) rang::fg::magenta<< str << rang::style::reset
#define CYAN(str) rang::fg::cyan<< str << rang::style::reset
#define BLACK(str) rang::fg::black<< str << rang::style::reset



//use 'non-optimized' computation of reason clauses -- tree-like without reordering and without skipping unneccessary repeated resolvents with the same clause
//NOTE there are very rare known bugs in the old implementation
#define TREE_LIKE_REASON_CLS_COMP


//type for variable numbering (must be unsigned; as (var_t)-1 must be bigger than all other values...)
typedef uint_fast32_t var_t;

//type for dl_counting
typedef uint_fast16_t dl_c_t; //change to something larger? this might overflow if we have dl > 65535... but in that case a solution is unlikely to be found anyways...

//type for cls length
typedef uint_fast16_t cls_size_t; //clauses with more than 65535 linerals are impractical!



//select allocator
template<class T>
//using allocator = std::allocator<T>;
//using allocator = boost::fast_pool_allocator<T, boost::default_user_allocator_new_delete, boost::details::pool::null_mutex, 64, 128>;
using allocator = boost::fast_pool_allocator<T, boost::default_user_allocator_malloc_free, boost::details::pool::null_mutex, 64, 128>;

//select vector impl to use
template<class T>
using vec = std::vector<T>;
//using vec = std::vector<T, allocator<T>>; //very poor performance
//using vec = boost::container::vector<T>;
//using vec = boost::container::stable_vector<T>;
//using vec = boost::container::vector<T, boost::container::allocator<T>>;
//using vec = boost::container::vector<T, boost::container::adaptive_pool<T>>;

template<class T>
//using list = std::list<T>;
using list = std::list<T, allocator<T> >;

template<class T>
using deque = std::deque<T>;


enum class bool3 { False, True, None };
inline bool3 to_bool3(const bool b) { return b ? bool3::True : bool3::False; };
inline bool3 neg(const bool3 b) { return b==bool3::None ? bool3::None : (b==bool3::True ? bool3::False : bool3::True); };
inline std::string b3_to_str(const bool3 b) { return b==bool3::None ? "None" : (b==bool3::True ? "True" : "False"); };
inline bool b3_to_bool(const bool3 b) { assert(b!=bool3::None); return b==bool3::True; };


class lineral_watch;

/**
 * @brief structure for storing equivalence of vars; essentially a pair of ind and polarity
 */
struct equivalence {
  var_t ind;
  var_t prev_ind;
  bool polarity;
  list<lineral_watch>::iterator reason_lin;
  var_t lvl;

  equivalence() : ind(0), prev_ind(0), polarity(false), lvl(-1) {};
  equivalence(const var_t _ind, const bool _polarity, const var_t _lvl) : ind(_ind), polarity(_polarity), lvl(_lvl) {};
  equivalence(const equivalence& other) = default;
  equivalence(equivalence&& other) = default;
  
  constexpr equivalence& operator=(const equivalence& o) = default;
  
  void set_ind(const var_t _ind) { ind = _ind; };
  void set_prev_ind(const var_t _ind) { prev_ind = _ind; };
  void set_polarity(const bool _polarity) { polarity = _polarity; };
  void set_lin(const list<lineral_watch>::iterator& reason_lin_) { reason_lin = reason_lin_; };
  void set_lvl(const var_t lvl_) { lvl = lvl_; };

  bool is_active() const { return ind>0; };
  bool is_active(const var_t lvl_) const { return ind>0 && lvl<=lvl_; };

  void clear() { ind = 0; lvl=0; };
  std::string to_str(const var_t& idx) const { return "x" + std::to_string(idx) + "+x" + std::to_string(ind) + (polarity ? "+1" : ""); };

  void swap(equivalence& o) noexcept {
    std::swap(ind, o.ind);
    std::swap(polarity, o.polarity);
    std::swap(reason_lin, o.reason_lin);
    std::swap(lvl, o.lvl);
  }
};

/**
 * @brief class that handles stores guessing path
 */
class guessing_path {
  private:
    vec<var_t> P;
    vec<bool> init_phase;

  public:
    guessing_path() {};
    guessing_path(const guessing_path& o) : P(o.P), init_phase(o.init_phase) {};
    guessing_path(guessing_path&& o) : P(std::move(o.P)), init_phase(std::move(o.init_phase)) {};

    std::size_t size() const noexcept { return P.size(); };

    void insert(const var_t& ind, const bool3 phase = bool3::False) {
      P.emplace_back(ind);
      init_phase.emplace_back(b3_to_bool(phase));
    };
    bool get_phase(const var_t& idx) const { return init_phase[idx]; };

    var_t operator [](const var_t& idx) const { return P[idx]; };

    bool assert_data_struct() const {
      assert(P.size() == init_phase.size());
      return true;
    };
};

/**
 * @brief options for decision heuristic
 * lex: proceed lexicographically
 * vsids: use vsids heuristic
 * lwl: choose variable with longest watch list
 * swl: choose variable with shortest watch list
 */
enum class dec_heu { vsids, lwl, lex, swl };

/**
 * @brief options for phase selection
 * rand: use random phases
 * save: save phases from last run
 * save_inv: use oppositve phase from last run
 */
enum class phase_opt { rand, save, save_inv };

/**
 * @brief options for conflict analysis
 * no: no conflict analysis --> DPLL solving
 * dpll: DPLL-style solving, but we add learnt clauses (should only be used for testing!)
 * fuip: first UIP conflict analysis
 */
enum class ca_alg { no, dpll, fuip, fuip_opt };

/**
 * @brief options for restart heuristic
 * no: no restarts
 * fixed: restart after a fixed number of conflicts
 * luby: restarts based on paper 'Optimal Speedup of Las Vegas Algorithms' by Luby et al.
 * lbd: exponential moving average LBD-based forcing/blocking restarts
 */
enum class restart_opt { no, fixed, luby, lbd};

/**
 * @brief options for initial propagation of non-forcing linerals
 * no: no propagation
 * nbu: 'no blow up'; only propagate if lineral's size does not 'blow up'
 * full: full propagation, i.e., reduction
 */
enum class initial_prop_opt { no, nbu, full};

/**
 * @brief options for xornado pre-/in-processing
 * no: no xornado/implication graph-based reasoning
 * scc: only use strongly connected components
 * scc_fls: use strongly connected components and failed lineral reasoning
 * 
 * @note pre-/inprocessing applied every time the solver does GCP in dl 0
 */
enum class xornado_preproc { no, scc, scc_fls};

/**
 * @brief struct that holds options for the various heuristic choices
 * 
 */
struct options {
    dec_heu dh = dec_heu::vsids;
    phase_opt po = phase_opt::save;

    ca_alg ca = ca_alg::fuip;
    bool cm = false;

    restart_opt rst = restart_opt::lbd;

    initial_prop_opt ip = initial_prop_opt::no;
    xornado_preproc pp = xornado_preproc::scc_fls;

    bool eq = true;

    bool lgj = true;

    int gauss_elim_schedule = 0;
    
    int verb = 0;

    int timeout = 0;

    unsigned int sol_count = 1;

    guessing_path P;

    const bool warm_restart = true;

    //default settings
    options() {};
    options(guessing_path P_) : P(P_) {};
    options(dec_heu dh_, phase_opt po_, ca_alg ca_, int gauss_elim_schedule_, int verb_, int timeout_=0) : dh(dh_), po(po_), ca(ca_), gauss_elim_schedule(gauss_elim_schedule_), verb(verb_), timeout(timeout_) {};
    options(dec_heu dh_, phase_opt po_, ca_alg ca_, bool cm_, restart_opt rst_, initial_prop_opt ip_, bool eq_, int gauss_elim_schedule_, int verb_) : dh(dh_), po(po_), ca(ca_), cm(cm_), rst(rst_), ip(ip_), eq(eq_), gauss_elim_schedule(gauss_elim_schedule_), verb(verb_) {};
    options(dec_heu dh_, phase_opt po_, ca_alg ca_, bool cm_, restart_opt rst_, initial_prop_opt ip_, xornado_preproc pp_, bool eq_, bool lgj_, int gauss_elim_schedule_, int verb_, int timeout_, unsigned int sol_count_, guessing_path P_) : dh(dh_), po(po_), ca(ca_), cm(cm_), rst(rst_), ip(ip_), pp(pp_), eq(eq_), lgj(lgj_), gauss_elim_schedule(gauss_elim_schedule_), verb(verb_), timeout(timeout_), sol_count(sol_count_), P(P_) {};
    options(const options& o) = default;

    std::string to_str() const {
      std::string str = "";

      str += "c dec_heu: ";
      switch(dec_heu(dh)) {
        case dec_heu::vsids: str += "vsids"; break;
        case dec_heu::lwl: str += "lwl"; break;
        case dec_heu::lex: str += "lex"; break;
        case dec_heu::swl: str += "swl"; break;
      }
      str += "\n";

      str += "c phase_opt: ";
      switch(phase_opt(po)) {
        case phase_opt::rand: str += "rand"; break;
        case phase_opt::save: str += "save"; break;
        case phase_opt::save_inv: str += "save_inv"; break;
      }
      str += "\n";

      str += "c ca_alg: ";
      switch(ca_alg(ca)) {
        case ca_alg::no: str += "no"; break;
        case ca_alg::dpll: str += "dpll"; break;
        case ca_alg::fuip: str += "fuip"; break;
        case ca_alg::fuip_opt: str += "fuip_opt"; break;
      }
      str += "\n";

      str += "c restart_opt: ";
      switch(restart_opt(rst)) {
        case restart_opt::no: str += "no"; break;
        case restart_opt::fixed: str += "fixed"; break;
        case restart_opt::luby: str += "luby"; break;
        case restart_opt::lbd: str += "lbd"; break;
      }
      str += "\n";
      
      str += "c initial_prop_opt: ";
      switch(initial_prop_opt(ip)) {
        case initial_prop_opt::no: str += "no"; break;
        case initial_prop_opt::nbu: str += "nbu"; break;
        case initial_prop_opt::full: str += "full"; break;
      }
      str += "\n";

      str += "c xornado_preproc: ";
      switch(xornado_preproc(pp)) {
        case xornado_preproc::no: str += "no"; break;
        case xornado_preproc::scc: str += "scc"; break;
        case xornado_preproc::scc_fls: str += "scc_fls"; break;
      }
      str += "\n";

      str += "c lazy-gauss: " + std::to_string(lgj) + "\n";
      
      str += "c gauss_elim_schedule: " + std::to_string(gauss_elim_schedule) + "\n";

      str += "c clause-minimization: " + std::to_string(cm) + "\n";
      
      str += "c eq: " + std::to_string(eq) + "\n";

      str += "c verb: " + std::to_string(verb) + "\n";

      str += "c timeout: " + std::to_string(timeout) + "\n";

      str += "c sol_count: " + std::to_string(sol_count);

      //str += "c guessing_path: ";
      //for(var_t i = 0; i < P.size(); i++) {
      //  str += std::to_string(P[i]) + (P.get_phase(i) ? "+1" : "-1") + " ";
      //}

      return str;
    }
};


/**
 * @brief struct storing stats info on solving call, contains solution(s) if intance is satisfiable
 */
class stats {
  public:
    bool finished = false;
    list<vec<bool>> sols;
    std::atomic<bool> cancelled = false;

    unsigned int no_dec = 0;
    unsigned int no_confl = 0;
    unsigned int no_lgj_prop = 0;
    unsigned int no_ge = 0;
    unsigned int no_ge_prop = 0;
    unsigned int no_ig = 0;
    unsigned int no_ig_prop = 0;
    unsigned int no_restarts = 0;
    unsigned int no_blocked_restarts = 0;
    unsigned int no_deletions = 0;
    unsigned int no_gcp = 0;
    unsigned int no_upd = 0;
    //newly learnt pure-xors via upd
    unsigned int new_px_upd = 0;

    std::chrono::high_resolution_clock::time_point begin = std::chrono::high_resolution_clock::time_point::min();
    std::chrono::high_resolution_clock::time_point end = std::chrono::high_resolution_clock::time_point::min();
    
    std::chrono::duration<double> total_linalg_time = std::chrono::duration<double>::zero();
    std::chrono::duration<double> total_lgj_time = std::chrono::duration<double>::zero();
    std::chrono::duration<double> total_ig_time = std::chrono::duration<double>::zero();
    std::chrono::duration<double> total_ca_time = std::chrono::duration<double>::zero();
    
    bool is_sat() const { return !sols.empty(); };

    void print_final() const {
      double time = static_cast<float>(std::chrono::duration_cast<std::chrono::milliseconds>(end - begin).count())/1000.0f;
      double linalg_time = static_cast<float>(std::chrono::duration_cast<std::chrono::milliseconds>(this->total_linalg_time).count())/1000.0f;
      double lgj_time = static_cast<float>(std::chrono::duration_cast<std::chrono::milliseconds>(this->total_lgj_time).count())/1000.0f;
      double ig_time = static_cast<float>(std::chrono::duration_cast<std::chrono::milliseconds>(this->total_ig_time).count())/1000.0f;
      double ca_time = static_cast<float>(std::chrono::duration_cast<std::chrono::milliseconds>(this->total_ca_time).count())/1000.0f;
      std::cout << std::fixed << std::setprecision(3);
      const auto width_time = std::to_string((int) time).length()+4;
      const auto width_int = std::min(10, (int) std::to_string(new_px_upd).length());

      std::cout << "c decisions      : " << std::setw(width_int) << no_dec << " (" << (float) no_dec/time  << " dec/sec)" << std::endl;
      std::cout << "c conflicts      : " << std::setw(width_int) << no_confl << " (" << (float) no_dec/no_confl  << " dec/confl)" << std::endl;
      std::cout << "c restarts       : " << std::setw(width_int) << no_restarts << " (" << (float) no_confl/no_restarts  << " confl/rst)" << std::endl;
      std::cout << "c blocked rst    : " << std::setw(width_int) << no_blocked_restarts << std::endl;
      std::cout << "c " << std::endl;

      std::cout << "c CGP props      : " << std::setw(width_int) << new_px_upd  << " (" << (float) no_lgj_prop/no_dec << " props/dec)" << std::endl;
      std::cout << "c LGJ props      : " << std::setw(width_int) << no_lgj_prop  << std::endl;
      std::cout << "c GE calls       : " << std::setw(width_int) << no_ge << std::endl;
      std::cout << "c GE props       : " << std::setw(width_int) << no_ge_prop  << " (" << (float) no_ge_prop/no_ge << " props/call)" << std::endl;
      std::cout << "c IG calls       : " << std::setw(width_int) << no_ig << std::endl;
      std::cout << "c IG props       : " << std::setw(width_int) << no_ig_prop  << " (" << (float) no_ig_prop/no_ig << " props/call)" << std::endl;
      std::cout << "c " << std::endl;

      std::cout << "c LGJ time       : " << std::setw(width_time) << (float) lgj_time << " [s] (" << (float) 100*lgj_time/time << " [%])" << std::endl;
      std::cout << "c GE time        : " << std::setw(width_time) << (float) linalg_time << " [s] (" << (float) 100*linalg_time/time << " [%])" << std::endl;
      std::cout << "c IG time        : " << std::setw(width_time) << (float) ig_time << " [s] (" << (float) 100*ig_time/time << " [%])" << std::endl;
      std::cout << "c CA time        : " << std::setw(width_time) << (float) ca_time     << " [s] (" << (float) 100*ca_time/time << " [%])" << std::endl;
      std::cout << "c Total time     : " << std::setw(width_time) << time << " [s]" << std::endl;
    }
    
    /**
     * @brief print final solution
     */
    void print_sol() const {
      if(finished) {
          const auto& sol = sols.back();
          if(sols.size()>0) {
              std::cout << "s SATISFIABLE" << std::endl;
              std::cout << "v ";
              for (var_t i = 1; i <= sol.size(); i++) {
                  std::cout << (sol[i-1] ? "" : "-") << std::to_string( i ) << " ";
              }
              std::cout << "0" << std::endl;
          } else {
              std::cout << "s UNSATISFIABLE" << std::endl;
          }
      } else {
              std::cout << "c timeout reached or interupted!" << std::endl;
              std::cout << "s INDEFINITE" << std::endl;
      }
    };
    
    void print_gcp_info() {
      float total_time = static_cast<float>(std::chrono::duration_cast<std::chrono::milliseconds>(end - begin).count())/1000.0f;
      std::cout << std::fixed << std::setprecision(3);
      std::cout << "c px by upd      : " << new_px_upd << std::endl;
      std::cout << "c GE prop        : " << no_ge << std::endl;
      std::cout << "c GE efficiacy   : " << (double) no_ge_prop/no_ge << std::endl;
      std::cout << "c Total time     : " << total_time << " [s]" << std::endl;
    };
    
    stats() {};
    ~stats() { /*std::cout << "destroying stats!" << std::endl;*/ };
    stats(stats& o) noexcept : finished(o.finished), sols(o.sols), no_dec(o.no_dec), no_confl(o.no_confl), no_ge(o.no_ge), no_ge_prop(o.no_ge_prop), no_restarts(o.no_restarts), new_px_upd(o.new_px_upd), begin(o.begin), end(o.end) {
      cancelled.store( o.cancelled.load() );
    }
    stats(stats&& o) noexcept : finished(std::move(o.finished)), sols(std::move(o.sols)), no_dec(std::move(o.no_dec)), no_confl(std::move(o.no_confl)), no_ge(std::move(o.no_ge)), no_ge_prop(std::move(o.no_ge_prop)), no_restarts(std::move(o.no_restarts)), new_px_upd(std::move(o.new_px_upd)), begin(std::move(o.begin)), end(std::move(o.end))  {
      cancelled.store( o.cancelled.load() );
    }
    stats(unsigned int no_dec_, unsigned int no_confl_, const list<vec<bool>>& sols_) : sols(sols_), no_dec(no_dec_), no_confl(no_confl_) {};
    stats(unsigned int no_dec_, unsigned int no_confl_) : no_dec(no_dec_), no_confl(no_confl_) {};

    stats& operator=(const stats& o) noexcept {
      finished = o.finished;
      sols = o.sols;
      no_dec = o.no_dec;
      no_confl = o.no_confl;
      no_ge = o.no_ge;
      no_ge_prop = o.no_ge_prop;
      no_restarts = o.no_restarts;
      no_gcp = o.no_gcp;
      no_upd = o.no_upd;
      begin = o.begin;
      end = o.end;
      cancelled.store( o.cancelled.load() );
      return *this;
    }
};

//functions for solving
class lineral;

/**
 * @brief solves xnf using provided opts
 * 
 * @param xnf vector of vector representing list of xor-clauses to be solved -- only works for 2-XNFs so far!
 * @param opts options specifying update alg, timeout, inprocessing settings etc
 * @param num_vars number of variables
 * @param s stats to put statistics into
 * 
 * @return int exit code
 */
int solve(const vec< vec<lineral> >& xnf, const var_t num_vars, const options& opts, stats& s);

stats solve(const vec< vec<lineral> >& xnf, const var_t num_vars, const options& opts);

/**
 * @brief perform one GCP on xnf using provided opts
 * 
 * @param xnf vector of vector representing list of xor-clauses to be solved -- only works for 2-XNFs so far!
 * @param opts options specifying update alg, timeout, inprocessing settings etc
 * @param num_vars number of variables
 * @param s stats to put statistics into
 */
std::string gcp_only(const vec< vec<lineral> >& xnf, const var_t num_vars, const options& opts, stats& s);

bool check_sol(const vec< vec<lineral> >& clss, const vec<bool>& sol);
bool check_sols(const vec< vec<lineral> >& clss, const list<vec<bool>>& sols);
