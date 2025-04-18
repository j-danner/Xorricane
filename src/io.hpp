// Copyright (c) 2022-2025 Julian Danner <julian@danner-web.de>
//
// Permission is hereby granted, free of charge, to any person obtaining a copy of
// this software and associated documentation files (the "Software"), to deal in
// the Software without restriction, including without limitation the rights to
// use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
// the Software, and to permit persons to whom the Software is furnished to do so,
// subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included in all
// copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
// FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
// COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
// IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
// CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

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
 * @param verbose true for verbosity output
 * @return parsed_xnf parsed num-cls, num-vars and parsed linerals
 */
parsed_xnf parse_file(const std::string& fname, bool verbose = false);

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
 * @param verbose true for verbosity output
 * @return guessing_path of variables
 */
guessing_path parse_gp(const std::string &fname, bool verbose = false);

void write_str(const std::string& fname, const std::string& out);

std::vector< std::string > split(const std::string& str, const std::string& delim);

