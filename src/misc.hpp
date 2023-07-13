#pragma once

//std
#include <atomic>
#include <stdint.h>
#include <cassert>
#include <chrono>
#include <vector>
#include <iostream>
#include <iomanip>
#include <string>
//other
#include <omp.h>

#include <boost/container/vector.hpp>
#include <boost/container/stable_vector.hpp>
#include <boost/container/allocator.hpp>
#include <boost/container/adaptive_pool.hpp>


//verbosity output
#ifdef VERBOSITY
  #define VERB(lvl, msg) if(opt.verb >= lvl) { std::cout << msg << std::endl; }
#else
  #define VERB(lvl, msg)
#endif


//type for variable numbering (16bit should suffice)
typedef uint16_t var_t;
//typedef uint_fast16_t var_t;

//type for cls length
typedef unsigned char cls_size_t;

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


/**
 * @brief structure for storing equivalence of vars; essentially a pair of ind and polarity
 * @todo bitpacking?
 */
struct equivalence {
  var_t ind;
  bool polarity;

  equivalence() : ind(0), polarity(false) {};
  equivalence(const var_t _ind, const bool _polarity) : ind(_ind), polarity(_polarity) {};
  equivalence(const equivalence& other) : ind(other.ind), polarity(other.polarity) {};
  equivalence(equivalence&& other) : ind(other.ind), polarity(other.polarity) {};
  
  void set_ind(const var_t _ind) { ind = _ind; };
  void set_polarity(const bool _polarity) { polarity = _polarity; };
};


enum class dec_heu { vsids, lwl, lex, swl };
enum class phase_opt { rand, save, save_inv };
enum class ca_alg { dpll, fuip };

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
    
    int jobs = omp_get_num_threads();
    
    int verb = 0;

    int timeout = 0;

    //default settings
    options() : num_vars(0), num_cls(0) {};
    options(var_t n_vars) : num_vars(n_vars), num_cls(0) {};
    options(var_t n_vars, var_t n_cls) : num_vars(n_vars), num_cls(n_cls) {};
    options(var_t n_vars, var_t n_cls, dec_heu dh_, phase_opt po_, ca_alg ca_, int jobs_, int verb_, int timeout_) : num_vars(n_vars), num_cls(n_cls), dh(dh_), po(po_), ca(ca_), jobs(jobs_), verb(verb_), timeout(timeout_) {};
};


/**
 * @brief struct returned by solver, contains bool sat telling if intance is satisfiable; if it is, also contains a solution
 * 
 */
class stats {
  public:
    bool finished = false;
    bool sat = false;
    vec<bool> sol;
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

    std::chrono::steady_clock::time_point begin;
    std::chrono::steady_clock::time_point end;

    void print_stats() {
      std::cout << "c v_upd     : " << no_vert_upd << std::endl;
      std::cout << "c restarts  : " << no_restarts << std::endl;
      std::cout << "c decisions : " << no_dec << std::endl;
      std::cout << "c conflicts : " << no_confl << std::endl;
    };

    void print_final() {
      float total_time = static_cast<float>(std::chrono::duration_cast<std::chrono::milliseconds>(end - begin).count())/1000.0f;
      std::cout << std::fixed << std::setprecision(3);

      std::cout << "c dec/sec    : "  << no_dec/total_time << std::endl;
      //std::cout << "c v_upd/sec  : " << no_vert_upd/total_time << std::endl;
      //std::cout << "c " << std::endl;
      //std::cout << "c v_upd/dec  : " << ((float) no_vert_upd)/((float) no_dec) << std::endl;
      //std::cout << "c " << std::endl;
      //std::cout << "c avg graph size : " << ((float) total_upd_no_v)/((float) no_graph_upd) << std::endl;
      std::cout << "c avg xsys size  : " << ((float) total_upd_xsys_size)/((float) no_gcp) << std::endl;
      //std::cout << "c " << std::endl;

      std::cout << "c px by upd  : " << new_px_upd << std::endl;
      std::cout << "c " << std::endl;

      //std::cout << "c vertex upd : " << no_vert_upd << std::endl;
      //std::cout << "c graph upd  : " << no_graph_upd << std::endl;
      std::cout << "c restarts   : " << no_restarts << std::endl;
      std::cout << "c decisions  : " << no_dec << std::endl;
      std::cout << "c conflicts  : " << no_confl << std::endl;
      std::cout << "c Total time : " << total_time << " [s]" << std::endl;

      if(finished) {
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
    
    stats() {};
    ~stats() { /*std::cout << "destroying stats!" << std::endl;*/ };
    stats(stats& o) noexcept : finished(o.finished), sat(o.sat), sol(o.sol), no_dec(o.no_dec), no_confl(o.no_confl), no_vert_upd(o.no_vert_upd), no_restarts(o.no_restarts), new_px_upd(o.new_px_upd), begin(o.begin), end(o.end) {
      cancelled.store( o.cancelled.load() );
    }
    stats(stats&& o) noexcept : finished(std::move(o.finished)), sat(std::move(o.sat)), sol(std::move(o.sol)), no_dec(std::move(o.no_dec)), no_confl(std::move(o.no_confl)), no_vert_upd(std::move(o.no_vert_upd)), no_restarts(std::move(o.no_restarts)), new_px_upd(std::move(o.new_px_upd)), begin(std::move(o.begin)), end(std::move(o.end))  {
      cancelled.store( o.cancelled.load() );
    }
    stats(unsigned int no_dec_, unsigned int no_confl_, const vec<bool>& sol_) : sat(true), sol(sol_), no_dec(no_dec_), no_confl(no_confl_) {};
    stats(unsigned int no_dec_, unsigned int no_confl_) : sat(false), no_dec(no_dec_), no_confl(no_confl_) {};

    stats& operator=(const stats& o) noexcept {
      finished = o.finished;
      sat = o.sat;
      sol = o.sol;
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

