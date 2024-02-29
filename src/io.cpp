#include "io.hpp"

#include <string>
#include <fstream>
#include <iostream>
#include <string>
#include <cstring>

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


parsed_xnf parse_file(std::istream& file) {
    var_t num_vars = 0;
    var_t num_cls = 0;
    
    vec< vec<xlit> > cls;
    vec< xlit > cl;
    vec< var_t > idxs;

    std::string line;
    while (std::getline(file, line)) {
        if (line.length() == 0 || line[0] == 'c') continue; //ignore line

        auto words = split(line, " ");
        if (words[0] == "p") {
            if (words[1] != "xnf") {
                std::cout << "c parser: file-format specified as \'" << words[1] << "\' continuing as if it were " << "\'xnf\'" << "." << std::endl;
            }
            if (words.size()<4) {
                std::cout << "c parser: file-format incorrectly specified. Should be \'p xnf n m\' where n is the number of variables and m the number of clauses." << std::endl;
            }
            num_vars = stoi(words[2]);
            num_cls = stoi(words[3]);
        } else {
            //line contains clause
            cl.clear();

            //check if clause is in XOR-clause notation or XNF-notation!
            if(words[0] == "x") {
                //convert to XNF-notation:
                words[0] = std::accumulate( std::next(words.begin(),2), std::prev(words.end()), words[1], [](std::string a, std::string b) { return a + "+" + b; });
                words[1] = "0";
                words.resize(2);
            }

            for (size_t i = 0; i < words.size(); i++)
            {
                //check if clause is terminated:
                if (words[i]=="0" || words[i]=="\0") {
                    break;
                }
                //otherwise read xlit
                auto lit = split(words[i], "+");
                idxs.clear();
                bool need_0 = true;
                for (auto &&v : lit) {
                    int v_ = stoi(v);
                    //std::cout << v << std::endl;
                    if (v_>0) {
                        idxs.emplace_back( v_ );
                        if ((var_t) v_ > num_vars) {
                            throw std::invalid_argument( "c provided clauses include larger vars than announced by header!" );
                        };
                    } else if (v_==0) {
                        //not standardized (interpret '+0' as '-')
                        need_0 ^= true;
                    } else {
                        idxs.emplace_back(  -v_ );
                        need_0 ^= true;
                    }
                }
                
                if (idxs.size() > 0) cl.emplace_back( std::move(idxs), need_0, presorted::no );
            }
            //add clause to cls
            if (cl.size() > 0) cls.emplace_back( std::move(cl) );
        }
    }

    if( cls.size() != num_cls) {
        std::cout << "c Number of clauses in header differs from number of found clauses!" << std::endl;
        std::cout << "c header said " << num_cls << " whereas we found " << cls.size() << " clauses." << std::endl;
    }
    
    return parsed_xnf(num_vars, num_cls, cls);
}


parsed_xnf parse_file(const std::string& fname) {
    std::istream file(NULL);
    if(fname!=" ") {
        std::ifstream file(fname);
        if ( file.fail() || !file.is_open() ) {
            std::cout << "c file \'" << fname << "\' not found!" << std::endl; //TODO do proper error handling, i.e., throw exception?!
            throw std::runtime_error("file not found!");
        }
        const auto p_xnf = parse_file( file );
        file.close();
        return p_xnf;
    } else {
        return parse_file( std::cin );
    }
}

std::string to_str(const vec< vec<xlit> >& xclss) {
    std::string str = "";
    for (auto &cls : xclss) {
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


guessing_path parse_gp(const std::string& fname) {
    guessing_path P;

    if(fname.size()==0) return P;

    std::ifstream file(fname);
    if ( file.fail() ) {
        std::cout << "c file \'" << fname << "\' not found!" << std::endl; //TODO do proper error handling, i.e., throw exception?!
        throw std::runtime_error("file not found!");
    }
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

    return P;
}

