#pragma once

#include "misc.hpp"
#include "lineral.hpp"


class lineral;
struct parsed_xnf {
    var_t num_vars;
    var_t num_cls;
    vec< vec<lineral> > cls;
};

/**
 * @brief parses file with name fname
 * 
 * @param fname xnf-file name
 * @return parsed_xnf parsed num-cls, num-vars and parsed linerals
 */
parsed_xnf parse_file(const std::string& fname);

/**
 * @brief print parsed cls to string
 * 
 * @param clss vector of cls (repr as vector of linerals)
 * @return std::string string repr of the xclauses
 */
std::string to_str(const vec< vec<lineral> >& clss);

/**
 * @brief parses file with name fname
 * 
 * @param fname guessing path file name; each line contains one index
 * @return guessing_path of variables
 */
guessing_path parse_gp(const std::string &fname);

void write_str(const std::string& fname, const std::string& out);

std::vector< std::string > split(const std::string& str, const std::string& delim);

