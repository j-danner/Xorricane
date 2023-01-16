//main func to start solving process!
#include "solve.hpp"

#include "solver.hpp"
#include <future>
#include <thread>
#include <chrono>
#include <csignal>
#include <fstream>
#include <functional>
#include <iostream>
#include <string>
#include <cstring>
#include <algorithm>
#include <stdexcept>



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


parsed_xnf parse_file(const std::string &fname) {
    var_t num_vars = 0;
    var_t num_cls = 0;
    
    vec< vec<xlit> > cls;

    std::ifstream file(fname);
    if ( file.fail() ) {
        std::cout << "c file \'" << fname << "\' not found!" << std::endl; //TODO do proper error handling, i.e., throw exception?!
        throw std::runtime_error("file not found!");
    }
    if (file.is_open()) {
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
                vec< xlit > cl;

                for (size_t i = 0; i < words.size(); i++)
                {
                    //check if clause is terminated:
                    if (words[i]=="0" || words[i]=="\0") {
                        break;
                    }
                    //otherwise read xlit
                    auto lit = split(words[i], "+");
                    vec< var_t > idxs;
                    bool need_0 = true;
                    for (auto &&v : lit)
                    {
                        int v_ = stoi(v);
                        //std::cout << v << std::endl;
                        if (v_>0) {
                            idxs.push_back( (var_t) v_ );
                            if (v_ > num_vars) {
                                throw std::invalid_argument( "c provided clauses include larger vars than announced by header!" );
                            };
                        } else if (v_==0) {
                            //not standard! (interprets '+0' as one '-')
                            need_0 ^= true;
                        } else {
                            idxs.push_back( (var_t) -v_ );
                            need_0 ^= true;
                        }
                    }
                    if (need_0) idxs.push_back( 0 );
                    
                    if (idxs.size() > 0) cl.push_back( xlit(idxs) );
                }
                //add clause to cls

                //NOTE here we assume that num_vars is large enough to fit all idxs!
                //if (cl.size() > 0) cls.push_back( xcls(cl, num_vars) );
                if (cl.size() > 0) cls.push_back( cl );
            }
        }
        file.close();
    }

    if( cls.size() != num_cls) {
        std::cout << "c Number of clauses in header differs from number of found clauses!" << std::endl;
        std::cout << "c header said " << num_cls << " whereas we found " << cls.size() << " clauses." << std::endl;
    }
    
    return parsed_xnf(num_vars, num_cls, cls);
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

//register signal-interupt handler using lambda with capture, adapted from 'https://stackoverflow.com/a/48164204/14352840'
namespace {
    std::function<void(int)> interrupt_handler;
    void signal_handler(int signal) { if(interrupt_handler) interrupt_handler(signal); }
} // namespace


//main solving func; solves xnf using opts!
void solve(const vec< vec<xlit> >& xnf, const options& opts, stats& s) {
    //set number of omp jobs!
    omp_set_num_threads(opts.jobs > omp_get_max_threads() ? omp_get_max_threads() : opts.jobs);

    //time comp, start
    s.begin = std::chrono::steady_clock::now();

    //std::cout << to_str( xnf ) << std::endl;
    auto sol = solver( xnf, opts );

    //register interupt handler
    std::signal(SIGINT, signal_handler);
    interrupt_handler = [&s]([[maybe_unused]] int signal) {
        std::cout << "!!! INTERRUPTED !!!" << std::endl;
        s.cancelled.store( true ); //make sure dpll_solve ends in next iteration!
    };

    //if timeout was set:
    if(opts.timeout>0) {
        auto timeout = std::chrono::seconds(opts.timeout);
        std::promise<int> p1;
        std::future<int> f_solve = p1.get_future();
        std::thread thr([&s,&sol](std::promise<int> p1){ sol.dpll_solve(s); p1.set_value_at_thread_exit(0); }, std::move(p1));
        thr.detach();

        std::future_status status = f_solve.wait_for(timeout);
        if(status != std::future_status::ready) { //if computation not finished
            std::cout << "c timeout reached!" << std::endl;
            s.cancelled.store( true ); //make thread terminate
            f_solve.wait(); //wait for thread to terminate fully!
        }
    } else {
        sol.dpll_solve(s);
    };
    
    //print stats
    s.end = std::chrono::steady_clock::now();
    s.print_final();
}

stats solve(const vec< vec<xlit> >& xnf, const options& opts) {
    stats s; solve(xnf, opts, s); return s;
}
