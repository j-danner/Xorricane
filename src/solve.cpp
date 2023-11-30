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

reordering parse_gp(const std::string& fname) {
    reordering P;

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
            P.insert((var_t) val, to_bool3(val_ < 0));
            already_inserted.insert((var_t) val);
        }
    }

    return P;
}

parsed_xnf parse_file(const std::string& fname) { reordering P; return parse_file_gp(fname, P); };
parsed_xnf parse_file_gp(const std::string &fname, const reordering& P) {
    var_t num_vars = 0;
    var_t num_cls = 0;
    
    vec< vec<xlit> > cls;
    vec< xlit > cl;
    vec< var_t > idxs;

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
                            idxs.emplace_back( P.at((var_t) v_) );
                            if ((var_t) v_ > num_vars) {
                                throw std::invalid_argument( "c provided clauses include larger vars than announced by header!" );
                            };
                        } else if (v_==0) {
                            //not standardized (interpret '+0' as '-')
                            need_0 ^= true;
                        } else {
                            idxs.emplace_back(  P.at((var_t) -v_) );
                            need_0 ^= true;
                        }
                    }
                    
                    if (idxs.size() > 0) cl.emplace_back( std::move(idxs), need_0, presorted::no );
                }
                //add clause to cls
                if (cl.size() > 0) cls.emplace_back( std::move(cl) );
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

void write_str(const std::string& fname, const std::string& out) {
    std::ofstream myfile;
    myfile.open (fname);
    myfile << out;
    myfile.close();
}

//register signal-interupt handler using lambda with capture, adapted from 'https://stackoverflow.com/a/48164204/14352840'
namespace {
    std::function<void(int)> interrupt_handler;
    void signal_handler(int signal) { if(interrupt_handler) interrupt_handler(signal); }
} // namespace


//main solving func; solves xnf using opts!
int solve(const vec< vec<xlit> >& xnf, const var_t num_vars, const options& opts, stats& s) {
    //set number of omp jobs!
    omp_set_num_threads(opts.jobs > omp_get_max_threads() ? omp_get_max_threads() : opts.jobs);

    //time comp, start
    if(s.begin==std::chrono::steady_clock::time_point::min()) s.begin = std::chrono::steady_clock::now();

    //std::cout << to_str( xnf ) << std::endl;
    auto sol = solver( xnf, num_vars, opts );

    //register interupt handler
    std::signal(SIGINT, signal_handler);
    interrupt_handler = [&s]([[maybe_unused]] int signal) {
        std::cout << "!!! INTERRUPTED !!!" << std::endl;
        s.cancelled.store( true ); //make sure cdcl_solve ends in next iteration!
    };

    //if timeout was set:
    if(opts.timeout>0) {
        auto timeout = std::chrono::seconds(opts.timeout);
        std::promise<int> p1;
        std::future<int> f_solve = p1.get_future();
        std::thread thr([&s,&sol](std::promise<int> p1){ sol.solve(s); p1.set_value_at_thread_exit(0); }, std::move(p1));
        thr.detach();

        std::future_status status = f_solve.wait_for(timeout);
        if(status != std::future_status::ready) { //if computation not finished
            std::cout << "c timeout reached!" << std::endl;
            s.cancelled.store( true ); //make thread terminate
            f_solve.wait(); //wait for thread to terminate fully!
        }
    } else {
        sol.solve(s);
    };
    
    //print stats
    s.end = std::chrono::steady_clock::now();
    if(opts.verb>0) s.print_final();

    const bool check_sol_flag = opts.verb == 0 || !s.finished || !s.sat || check_sols(xnf, s.sols);
    
    s.print_sol();
    if(opts.sol_count>1) std::cout << "c solutions found: "+std::to_string( std::count_if(s.sols.begin(),s.sols.end(), [](const vec<bool>& sol){ return sol.size()>0; } ) ) << std::endl;
        
    if(opts.verb > 0 && s.finished && s.sat) { //check sol!
        if(check_sol_flag) {
            std::cout << "c solution verified" << std::endl;
            return 0;
        } else {
            std::cout << "c solution INCORRECT!" << std::endl;
            return 1;
        }
    } else {
        return 0;
    }
}

stats solve(const vec< vec<xlit> >& xnf, const var_t num_vars, const options& opts) {
    stats s; solve(xnf, num_vars, opts, s); return s;
}

//perform one gcp run
std::string gcp_only(const vec< vec<xlit> >& xnf, const var_t num_vars, const options& opts, stats& s) {
    //set number of omp jobs!
    omp_set_num_threads(opts.jobs > omp_get_max_threads() ? omp_get_max_threads() : opts.jobs);

    //time comp, start
    s.begin = std::chrono::steady_clock::now();

    //std::cout << to_str( xnf ) << std::endl;
    auto sol = solver( xnf, num_vars, opts );

    //register interupt handler
    std::signal(SIGINT, signal_handler);
    interrupt_handler = [&s]([[maybe_unused]] int signal) {
        std::cout << "!!! INTERRUPTED !!!" << std::endl;
        s.cancelled.store( true ); //make sure cdcl_solve ends in next iteration!
    };

    //if timeout was set:
    std::string out = "";
    if(opts.timeout>0) {
        auto timeout = std::chrono::seconds(opts.timeout);
        std::promise<int> p1;
        std::future<int> f_solve = p1.get_future();
        std::thread thr([&out,&s,&sol](std::promise<int> p1)
            {
                do { sol.GCP(s); } while( sol.initial_linalg_inprocessing(s) );
                out = sol.to_xnf_str();
                p1.set_value_at_thread_exit(0);
            }, std::move(p1));
        thr.detach();

        std::future_status status = f_solve.wait_for(timeout);
        if(status != std::future_status::ready) { //if computation not finished
            std::cout << "c timeout reached!" << std::endl;
            s.cancelled.store( true ); //make thread terminate
            f_solve.wait(); //wait for thread to terminate fully!
        }
    } else {
        do { sol.GCP(s); } while( sol.initial_linalg_inprocessing(s) );
        out = sol.to_xnf_str();
    };
    
    //print stats
    s.end = std::chrono::steady_clock::now();
    if(opts.verb>0) s.print_gcp_info();
    return out;
}