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

#include "io.hpp"

#include <string>
#include <fstream>
#include <iostream>
#include <string>
#include <cstring>
#include <numeric>

//helper func
std::vector< std::string > split(const std::string& str, const std::string& delim) {
    std::vector< std::string > out;
    std::vector<char> writable(str.begin(), str.end());
    writable.push_back('\0');
    char* c_str = &writable[0];

    char * pch;
    pch = std::strtok(c_str, delim.c_str());
    while (pch != NULL)
    {
        out.push_back( std::string(pch) );
        pch = std::strtok(NULL, delim.c_str());
    }

    //make sure at least one empty string is in 'out':
    if(!out.size()) out.push_back("");

    return out;
}


parsed_xnf parse_file(std::istream& file, bool verbose) {
    var_t num_vars = 0;
    var_t actual_num_vars = 0;
    var_t num_cls = 0;
    var_t actual_num_cls = 0;
    
    vec< vec<lineral> > cls;
    vec< lineral > cl;
    std::set< var_t > idxs;

    int v_ = 0;

    std::string line;
    while (std::getline(file, line)) {
        if (line.length() == 0 || line[0] == 'c') continue; //ignore line

        auto words = split(line, " ");
        if (words[0] == "p") {
            if(verbose) std::cout << "c found header: " << line << std::endl;
            if (words[1] != "xnf") {
                if(verbose) std::cout << "c parser: file-format specified as \'" << words[1] << "\' continuing as if it were " << "\'xnf\'" << "." << std::endl;
            }
            if (words.size()<4) {
                if(verbose) std::cout << "c parser: file-format incorrectly specified. Should be \'p xnf n m\' where n is the number of variables and m the number of clauses." << std::endl;
            }
            num_vars = stoi(words[2]);
            num_cls = stoi(words[3]);
        } else if (words.size()>0) {
            //line contains clause
            cl.clear();

            if(*(words.rbegin())!="0") { throw std::runtime_error("incorrectly terminated clause '" + line + "' encountered!"); }
            
            //check if clause is in XOR-clause notation or XNF-notation!
            if(words[0] == "x") {
                //convert to XNF-notation:
                words[0] = std::accumulate( std::next(words.begin(),2), std::prev(words.end()), words[1], [](std::string a, std::string b) { return a + "+" + b; });
                words[1] = "0";
                words.resize(2);
            }

            //parse linerals -- if there is none, we have an empty clause!
            if(words.size()==1) {
                cl.emplace_back( 0, false );
            }
            //otherwise process remaining linerals
            for (size_t i = 0; i < words.size()-1; i++) {
                auto lit = split(words[i], "+");
                idxs.clear();
                bool need_0 = true;
                for (auto &&v : lit) {
                    v_ = stoi(v);
                    //std::cout << v << std::endl;
                    if (v_>0) {
                        if(idxs.contains(v_)) idxs.erase(v_);
                        else                  idxs.emplace(v_);
                        actual_num_vars = std::max( (var_t) v_, actual_num_vars );
                    } else if (v_==0) {
                        //not standardized (interpret '+0' as '-')
                        need_0 ^= true;
                    } else {
                        v_ = -v_;
                        if(idxs.contains(v_)) idxs.erase(v_);
                        else                   idxs.emplace(v_);
                        need_0 ^= true;
                        actual_num_vars = std::max( (var_t) v_, actual_num_vars );
                    }
                }
                //put lineral into clause -- if it is not 0 (!)
                if (idxs.size() > 0 || need_0) {
                    cl.emplace_back( vec<var_t>(idxs.begin(),idxs.end()), need_0, presorted::yes );
                } else {
                    //clause contains 0-lineral, i.e., is trivially satisfied and can be skipped!
                    cl.clear();
                    break;
                }
            }
            //add clause to cls -- if non-empty!
            if (cl.size() > 0) cls.emplace_back( std::move(cl) );
            else               { --num_cls; ++actual_num_cls; }
        }
    }

    if( cls.size() != num_cls) {
        if(verbose) std::cerr << "c Number of clauses in header differs from number of found clauses!" << std::endl;
        if(verbose) std::cerr << "c header said " << num_cls << " whereas we found " << cls.size() << " clauses." << std::endl;
        num_cls = cls.size();
    }
    if(actual_num_vars > num_vars) {
        if(verbose) std::cerr << "c Number of variables in header differs from number of found variables!" << std::endl;
        if(verbose) std::cerr << "c header said " << num_vars << " whereas we found " << actual_num_vars << " variables." << std::endl;
        num_vars = actual_num_vars;
    }

    if(verbose) std::cout << "c parsed " << num_cls << " clauses and " << num_vars << " variables." << std::endl;
    
    return parsed_xnf(num_vars, num_cls, cls);
}


parsed_xnf parse_file(const std::string& fname, bool verbose) {
    std::istream file(NULL);
    if(fname!=" ") {
        std::ifstream file(fname);
        if ( file.fail() || !file.is_open() ) {
            throw std::runtime_error("file \'" + fname + "\' not found!");
        }
        if(verbose) std::cout << "c reading XNF from " << fname << std::endl;
        const auto p_xnf = parse_file( file, verbose );
        file.close();
        return p_xnf;
    } else {
        if(verbose) std::cout << "c reading XNF from standard input" << std::endl;
        return parse_file( std::cin, verbose );
    }
}

std::string to_str(const vec< vec<lineral> >& clss) {
    std::string str = "";
    for (auto &cls : clss) {
        for (auto &&l : cls) {
            str.append( l.to_str() + " " );
        }
        str.append("\n");
    }
    return str;
}

void write_str(const std::string& fname, const std::string& out) {
    std::ofstream myfile;
    myfile.open (fname);
    myfile << out;
    myfile.close();
}


guessing_path parse_gp(const std::string& fname, bool verbose) {
    guessing_path P;

    if(fname.size()==0) return P;

    std::ifstream file(fname);
    if ( file.fail() ) {
        throw std::runtime_error("file \'" + fname + "\' not found!");
    }
    if(verbose) std::cout << "c reading gp from " << fname << std::endl;
    std::set<var_t> already_inserted;
    if(file.is_open()) {
        std::string line;
        while (std::getline(file, line)) {
            if (line.length() == 0 || line[0] == 'c') continue; //ignore line
            auto words = split(line, " ");
            const int val_ = stoi(words[0]);
            const int val = std::abs(val_);
            assert(val>0);

            if(already_inserted.contains((var_t) val)) continue;
            P.insert((var_t) val, to_bool3(val_ > 0));
            already_inserted.insert((var_t) val);
        }
    }
    file.close();

    return P;
}

