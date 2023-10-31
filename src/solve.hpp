#pragma once
//offers function to solve (and parse) xnf instances and guessing path files

#include <set>

#include "misc.hpp"
#include "xlit/xlit.hpp"

/**
 * @brief solves xnf using provided opts
 * 
 * @param xnf vector of vector representing list of xor-clauses to be solved -- only works for 2-XNFs so far!
 * @param opts options specifying update alg, timeout, inprocessing settings etc
 * @param s stats to put statistics into
 * 
 * @return int exit code
 */
int solve(const vec< vec<xlit> >& xnf, const options& opts, stats& s);

stats solve(const vec< vec<xlit> >& xnf, const options& opts);

/**
 * @brief perform one GCP on xnf using provided opts
 * 
 * @param xnf vector of vector representing list of xor-clauses to be solved -- only works for 2-XNFs so far!
 * @param opts options specifying update alg, timeout, inprocessing settings etc
 * @param s stats to put statistics into
 */
std::string gcp_only(const vec< vec<xlit> >& xnf, const options& opts, stats& s);

/**
 * @brief writes string to file
 * 
 * @param fname file path
 * @param out string to write
 */
void write_str(const std::string& fname, const std::string& out);

/**
 * @brief parses file with name fname
 * 
 * @param fname guessing path file name; each line contains one index
 * @return reordering of variables, s.t. lex is the correct order
 */
reordering parse_gp(const std::string& fname);

struct parsed_xnf {
    var_t num_vars;
    var_t num_cls;
    vec< vec<xlit> > cls;

    parsed_xnf(var_t _num_vars, var_t _num_cls, vec< vec<xlit> > _cls) : num_vars(_num_vars), num_cls(_num_cls), cls(_cls) {};
    parsed_xnf(const parsed_xnf& o) : num_vars(o.num_vars), num_cls(o.num_cls), cls(o.cls) {};
};

/**
 * @brief parses file with name fname
 * 
 * @param fname xnf-file name
 * @param reordering permutation of indices
 * @return parsed_Xnf parsed num-cls, num-vars and parsed xlits
 */
parsed_xnf parse_file_gp(const std::string& fname, const reordering& P);

/**
 * @brief parses file with name fname
 * 
 * @param fname xnf-file name
 * @return parsed_Xnf parsed num-cls, num-vars and parsed xlits
 */
parsed_xnf parse_file(const std::string& fname);

/**
 * @brief print parsed xcls to string
 * 
 * @param xclss vector of xcls (repr as vector of xlits)
 * @return std::string string repr of the xclauses
 */
std::string to_str(const vec< vec<xlit> >& xclss);

/**
 * @brief checks whether sol is a solution of given xcls
 * 
 * @param clss vector of xcls (repr as vector of xlits)
 * @param sol solution to be checked
 * @return true iff sol is a solution of the xclauses
 */
inline bool check_sol(const vec< vec<xlit> >& clss, const vec<bool>& sol) {
    return std::all_of( clss.begin(), clss.end(), /* all clauses need to be satisfied */
                    [&sol] (vec<xlit> xcls) -> bool { 
                        return std::any_of(xcls.begin(), xcls.end(), [&sol](xlit l) { return l.eval(sol); } ); /* at least one lit of clause must be satisfied */
                        }
                    );
}
