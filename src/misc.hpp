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
//other
#include <omp.h>
#include "robin_hood-3.11.5/robin_hood.h"

#include <boost/container/vector.hpp>
#include <boost/container/stable_vector.hpp>
#include <boost/container/allocator.hpp>
#include <boost/container/adaptive_pool.hpp>

//#define USE_EQUIV
//#define DEBUG_SLOW

//verbosity output
#ifdef VERBOSITY
  #define VERB(lvl, msg) if(opt.verb >= lvl) { std::cout << msg << std::endl; }
#else
  #define VERB(lvl, msg)
#endif

#define BOLD(str) ("\x1b[1m"+str+"\x1b[0m")

#if defined(DEBUG_SLOW) && !defined(NDEBUG)
  #define assert_slow(expr) assert(expr)
#else
  #define assert_slow(expr) {}
#endif



//type for variable numbering (must be unsigned; as (var_t)-1 must be bigger than all other values...)
typedef uint_fast32_t var_t;

//type for dl_counting
typedef uint_fast16_t dl_c_t; //change to something larger? this might overflow if we have dl > 65535... but in that case a solution is unlikely to be found anyways...

//type for cls length
typedef uint_fast8_t cls_size_t; //clauses with more than 256 linerals are impractical!

//select vector impl to use
template<class T>
using vec = std::vector<T>;
//using vec = boost::container::vector<T>;
//using vec = boost::container::stable_vector<T>;
//using vec = boost::container::vector<T, boost::container::allocator<T>>;
//using vec = boost::container::vector<T, boost::container::adaptive_pool<T>>;


enum class bool3 { False, True, None };
inline bool3 to_bool3(const bool b) { return b ? bool3::True : bool3::False; };
inline bool3 neg(const bool3 b) { return b==bool3::None ? bool3::None : (b==bool3::True ? bool3::False : bool3::True); };
inline std::string b3_to_str(const bool3 b) { return b==bool3::None ? "None" : (b==bool3::True ? "True" : "False"); };
inline bool b3_to_bool(const bool3 b) { assert(b!=bool3::None); return b==bool3::True ? true : false; };


#ifdef USE_EQUIV
/**
 * @brief structure for storing equivalence of vars; essentially a pair of ind and polarity
 * @todo bitpacking?
 */
struct equivalence {
  var_t ind;
  bool polarity;
  var_t reason;

  equivalence() : ind(0), polarity(false), reason(-1) {};
  equivalence(const var_t _ind, const bool _polarity) : ind(_ind), polarity(_polarity) {};
  equivalence(const equivalence& other) : ind(other.ind), polarity(other.polarity) {};
  equivalence(equivalence&& other) : ind(other.ind), polarity(other.polarity) {};
  
  void set_ind(const var_t _ind) { ind = _ind; };
  void set_polarity(const bool _polarity) { polarity = _polarity; };
  void set_reason(const var_t _reason) { reason = _reason; };

  void clear() { ind = 0; polarity = false; reason = -1; };
  std::string to_str(const var_t& idx) const { return "x" + std::to_string(idx) + "+x" + std::to_string(ind) + (polarity ? "+1" : ""); };
};
#else
struct equivalence {};
#endif

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
      init_phase.emplace_back(phase);
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
 */
enum class restart_opt { no, fixed, luby};

/**
 * @brief struct that holds options for the various heuristic choices
 * 
 */
struct options {
    dec_heu dh = dec_heu::vsids;
    phase_opt po = phase_opt::save;

    ca_alg ca = ca_alg::fuip;
    restart_opt rst = restart_opt::luby;

    int lin_alg_schedule = 0;
    
    int jobs = omp_get_num_threads();
    
    int verb = 0;

    int timeout = 0;

    unsigned int sol_count = 1;

    guessing_path P;

    //default settings
    options() {};
    options(guessing_path P_) : P(P_) {};
    options(dec_heu dh_, phase_opt po_, ca_alg ca_, int lin_alg_schedule_, int verb_, int timeout_=0) : dh(dh_), po(po_), ca(ca_), lin_alg_schedule(lin_alg_schedule_), verb(verb_), timeout(timeout_) {};
    options(dec_heu dh_, phase_opt po_, ca_alg ca_, int lin_alg_schedule_, int jobs_, int verb_, int timeout_) : dh(dh_), po(po_), ca(ca_), lin_alg_schedule(lin_alg_schedule_), jobs(jobs_), verb(verb_), timeout(timeout_) {};
    options(dec_heu dh_, phase_opt po_, ca_alg ca_, restart_opt rst_, int lin_alg_schedule_, int jobs_, int verb_, int timeout_, unsigned int sol_count_, guessing_path P_) : dh(dh_), po(po_), ca(ca_), rst(rst_), lin_alg_schedule(lin_alg_schedule_), jobs(jobs_), verb(verb_), timeout(timeout_), sol_count(sol_count_), P(P_) {};

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
      }
      str += "\n";

      str += "c lin_alg_schedule: " + std::to_string(lin_alg_schedule) + "\n";

      str += "c jobs: " + std::to_string(jobs) + "\n";

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
 * @brief struct returned by solver, contains bool sat telling if intance is satisfiable; if it is, also contains a solution
 * 
 */
class stats {
  public:
    bool finished = false;
    bool sat = false;
    std::list<vec<bool>> sols;
    std::atomic<bool> cancelled = false;

    unsigned int no_dec = 0;
    unsigned int no_confl = 0;
    unsigned int no_linalg = 0;
    unsigned int no_linalg_prop = 0;
    unsigned int no_restarts = 0;
    unsigned int no_gcp = 0;
    unsigned int no_upd = 0;
    //newly learnt pure-xors via upd
    unsigned int new_px_upd = 0;

    std::chrono::steady_clock::time_point begin = std::chrono::steady_clock::time_point::min();
    std::chrono::steady_clock::time_point end = std::chrono::steady_clock::time_point::min();

    void print_stats() const {
      std::cout << "c restarts  : " << no_restarts << std::endl;
      std::cout << "c decisions : " << no_dec << std::endl;
      std::cout << "c conflicts : " << no_confl << std::endl;
    };

    void print_final() const {
      float total_time = static_cast<float>(std::chrono::duration_cast<std::chrono::milliseconds>(end - begin).count())/1000.0f;
      std::cout << std::fixed << std::setprecision(3);

      std::cout << "c dec/sec        : "  << no_dec/total_time << std::endl;

      std::cout << "c px by upd      : " << new_px_upd << std::endl;
      std::cout << "c LA prop        : " << no_linalg << std::endl;
      std::cout << "c LA efficiacy   : " << (double) no_linalg_prop/no_linalg << std::endl;
      std::cout << "c " << std::endl;

      std::cout << "c restarts       : " << no_restarts << std::endl;
      std::cout << "c decisions      : " << no_dec << std::endl;
      std::cout << "c conflicts      : " << no_confl << std::endl;
      std::cout << "c Total time     : " << total_time << " [s]" << std::endl;
    }
    
    /**
     * @brief print final solution
     */
    void print_sol() const {
      if(finished) {
          const auto& sol = sols.back();
          if(sat) {
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
      std::cout << "c LA prop        : " << no_linalg << std::endl;
      std::cout << "c LA efficiacy   : " << (double) no_linalg_prop/no_linalg << std::endl;
      std::cout << "c Total time     : " << total_time << " [s]" << std::endl;
    };
    
    stats() {};
    ~stats() { /*std::cout << "destroying stats!" << std::endl;*/ };
    stats(stats& o) noexcept : finished(o.finished), sat(o.sat), sols(o.sols), no_dec(o.no_dec), no_confl(o.no_confl), no_linalg(o.no_linalg), no_linalg_prop(o.no_linalg_prop), no_restarts(o.no_restarts), new_px_upd(o.new_px_upd), begin(o.begin), end(o.end) {
      cancelled.store( o.cancelled.load() );
    }
    stats(stats&& o) noexcept : finished(std::move(o.finished)), sat(std::move(o.sat)), sols(std::move(o.sols)), no_dec(std::move(o.no_dec)), no_confl(std::move(o.no_confl)), no_linalg(std::move(o.no_linalg)), no_linalg_prop(std::move(o.no_linalg_prop)), no_restarts(std::move(o.no_restarts)), new_px_upd(std::move(o.new_px_upd)), begin(std::move(o.begin)), end(std::move(o.end))  {
      cancelled.store( o.cancelled.load() );
    }
    stats(unsigned int no_dec_, unsigned int no_confl_, const std::list<vec<bool>>& sols_) : sat(true), sols(sols_), no_dec(no_dec_), no_confl(no_confl_) {};
    stats(unsigned int no_dec_, unsigned int no_confl_) : sat(false), no_dec(no_dec_), no_confl(no_confl_) {};

    stats& operator=(const stats& o) noexcept {
      finished = o.finished;
      sat = o.sat;
      sols = o.sols;
      no_dec = o.no_dec;
      no_confl = o.no_confl;
      no_linalg = o.no_linalg;
      no_linalg_prop = o.no_linalg_prop;
      no_restarts = o.no_restarts;
      no_gcp = o.no_gcp;
      no_upd = o.no_upd;
      begin = o.begin;
      end = o.end;
      cancelled.store( o.cancelled.load() );
      return *this;
    }

};

