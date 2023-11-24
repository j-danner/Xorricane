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

//verbosity output
#ifdef VERBOSITY
  #define VERB(lvl, msg) if(opt.verb >= lvl) { std::cout << msg << std::endl; }
#else
  #define VERB(lvl, msg)
#endif

#define BOLD(str) ("\x1b[1m"+str+"\x1b[0m")


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
 * @brief class that handles reordering according to guessing path
 */
class reordering {
  private:
    //TODO use faster hashmap
  //#ifdef NDEBUG
  //  robin_hood::unordered_flat_map<var_t,var_t> P;
  //#else
    std::unordered_map<var_t,var_t> P;
  //#endif
    vec<bool> init_phase;
    var_t pos = 0;
  #ifndef NDEBUG
    var_t max = 0;
  #endif

  public:
    reordering() {};
    reordering(const reordering& o) : P(o.P), init_phase(o.init_phase), pos(o.pos) {};
    reordering(reordering&& o) : P(std::move(o.P)), init_phase(std::move(o.init_phase)), pos(o.pos) {};

    std::size_t size() const noexcept { return pos; };

    void insert(const var_t& ind, const bool3 phase = bool3::False) {
      init_phase.push_back(phase == bool3::True);
      ++pos;
    #ifndef NDEBUG
      max = std::max(std::max(pos, ind) , max);
    #endif
      if(at(pos)==ind) return;
      const auto P_ind = at(ind);
      const auto P_pos = at(pos);
      P[pos] = P_ind;
      P[ind] = P_pos;
    };
    const var_t& at(const var_t& ind) const noexcept { return P.contains(ind) ? P.at(ind) : ind; };
    bool get_phase(const var_t& idx) const { return init_phase[idx]; };

  #ifndef NDEBUG
    bool assert_data_stuct() const {
      std::set<var_t> tmp;
      for(var_t i=1; i<=max; ++i) {
        var_t P_i = at(i);
        assert(0 < P_i && P_i <= max);
        tmp.insert( P_i );
      }
      for(var_t i=1; i<=max; ++i) {
        if( !tmp.contains(i) ) {
          std::cout << "c reordering: missing index " << i << std::endl;
        }
        assert(tmp.contains(i));
      }
      assert( tmp.size() == max );
      assert( size() == init_phase.size() );
      return true;
    };
  #else
    bool assert_data_struct() const { return true };
  #endif
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
    var_t num_vars = 0;
    var_t num_cls = 0;

    dec_heu dh = dec_heu::vsids;
    phase_opt po = phase_opt::save;

    ca_alg ca = ca_alg::fuip;
    restart_opt rst = restart_opt::luby;
    
    int jobs = omp_get_num_threads();
    
    int verb = 0;

    int timeout = 0;

    unsigned int sol_count = 1;

    reordering P;

    //default settings
    options() : num_vars(0), num_cls(0) {};
    options(var_t n_vars) : num_vars(n_vars), num_cls(0) {};
    options(var_t n_vars, var_t n_cls) : num_vars(n_vars), num_cls(n_cls) {};
    options(var_t n_vars, var_t n_cls, reordering P_) : num_vars(n_vars), num_cls(n_cls), P(P_) {};
    options(var_t n_vars, var_t n_cls, dec_heu dh_, phase_opt po_, ca_alg ca_, int jobs_, int verb_, int timeout_) : num_vars(n_vars), num_cls(n_cls), dh(dh_), po(po_), ca(ca_), jobs(jobs_), verb(verb_), timeout(timeout_) {};
    options(var_t n_vars, var_t n_cls, dec_heu dh_, phase_opt po_, ca_alg ca_, restart_opt rst_, int jobs_, int verb_, int timeout_, unsigned int sol_count_, reordering P_) : num_vars(n_vars), num_cls(n_cls), dh(dh_), po(po_), ca(ca_), rst(rst_), jobs(jobs_), verb(verb_), timeout(timeout_), sol_count(sol_count_), P(P_) {};
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
    unsigned int no_vert_upd = 0;
    unsigned int no_restarts = 0;
    unsigned int no_graph_upd = 0;
    unsigned int no_gcp = 0;
    unsigned int no_upd = 0;
    unsigned int total_upd_no_v = 0;
    unsigned int total_upd_xsys_size = 0;
    //newly learnt pure-xors via upd
    unsigned int new_px_upd = 0;

    std::chrono::steady_clock::time_point begin = std::chrono::steady_clock::time_point::min();
    std::chrono::steady_clock::time_point end = std::chrono::steady_clock::time_point::min();

    void print_stats() const {
      std::cout << "c v_upd     : " << no_vert_upd << std::endl;
      std::cout << "c restarts  : " << no_restarts << std::endl;
      std::cout << "c decisions : " << no_dec << std::endl;
      std::cout << "c conflicts : " << no_confl << std::endl;
    };

    void print_final() const {
      float total_time = static_cast<float>(std::chrono::duration_cast<std::chrono::milliseconds>(end - begin).count())/1000.0f;
      std::cout << std::fixed << std::setprecision(3);

      std::cout << "c dec/sec    : "  << no_dec/total_time << std::endl;
      std::cout << "c avg xsys size  : " << ((float) total_upd_xsys_size)/((float) no_gcp) << std::endl;

      std::cout << "c px by upd  : " << new_px_upd << std::endl;
      std::cout << "c " << std::endl;

      std::cout << "c restarts   : " << no_restarts << std::endl;
      std::cout << "c decisions  : " << no_dec << std::endl;
      std::cout << "c conflicts  : " << no_confl << std::endl;
      std::cout << "c Total time : " << total_time << " [s]" << std::endl;
    }
    
    void reorder_sol(const reordering& P) {
      if(sols.size()==0) return;
      vec<bool> Psol(sols.back());
      for(var_t i=1; i <= sols.back().size(); ++i) {
        Psol[i-1] = sols.back()[P.at(i)-1];
      }
      sols.back() = std::move(Psol);
    }

    void reorder_sols(const reordering& P) {
      for(auto& sol : sols) {
        if(sol.size()==0) return;
        vec<bool> Psol(sol);
        for(var_t i=1; i <= sol.size(); ++i) {
          Psol[i-1] = sol[P.at(i)-1];
        }
        sol = std::move(Psol);
      }
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
    
    /**
     * @brief print last sol of sols
     * 
     * @param reordering P that should be applied prior to printing
     */
    void print_sol(const reordering& P) const {
      if(finished) {
          const auto& sol = sols.back();
          if(sat) {
              std::cout << "s SATISFIABLE" << std::endl;
              std::cout << "v ";
              for (var_t i = 1; i <= sol.size(); i++) {
                  std::cout << (sol[P.at(i)-1] ? "" : "-") << std::to_string( i ) << " ";
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
      std::cout << "c px by upd  : " << new_px_upd << std::endl;
      std::cout << "c Total time : " << total_time << " [s]" << std::endl;
    };
    
    stats() {};
    ~stats() { /*std::cout << "destroying stats!" << std::endl;*/ };
    stats(stats& o) noexcept : finished(o.finished), sat(o.sat), sols(o.sols), no_dec(o.no_dec), no_confl(o.no_confl), no_vert_upd(o.no_vert_upd), no_restarts(o.no_restarts), new_px_upd(o.new_px_upd), begin(o.begin), end(o.end) {
      cancelled.store( o.cancelled.load() );
    }
    stats(stats&& o) noexcept : finished(std::move(o.finished)), sat(std::move(o.sat)), sols(std::move(o.sols)), no_dec(std::move(o.no_dec)), no_confl(std::move(o.no_confl)), no_vert_upd(std::move(o.no_vert_upd)), no_restarts(std::move(o.no_restarts)), new_px_upd(std::move(o.new_px_upd)), begin(std::move(o.begin)), end(std::move(o.end))  {
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
      no_vert_upd = o.no_vert_upd;
      no_restarts = o.no_restarts;
      no_gcp = o.no_gcp;
      no_upd = o.no_upd;
      begin = o.begin;
      end = o.end;
      cancelled.store( o.cancelled.load() );
      return *this;
    }

};

