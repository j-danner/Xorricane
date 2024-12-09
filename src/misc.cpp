#include "solver.hpp"
#include "misc.hpp"
#include "lineral.hpp"

#include <future>
#include <thread>
#include <chrono>
#include <csignal>
#include <algorithm>
#include <stdexcept>

//register signal-interupt handler using lambda with capture, adapted from 'https://stackoverflow.com/a/48164204/14352840'
namespace {
    std::function<void(int)> interrupt_handler;
    void signal_handler(int signal) { if(interrupt_handler) interrupt_handler(signal); }
} // namespace

//main solving func; solves xnf using opts! -- returns 10 for SAT, 20 for UNSAT, 0 for timeout
int solve(const vec< vec<lineral> >& xnf, const var_t num_vars, const options& opts, stats& s) {
    //time comp, start
    if(s.begin==std::chrono::high_resolution_clock::time_point::min()) s.begin = std::chrono::high_resolution_clock::now();

    //std::cout << to_str( xnf ) << std::endl;
    solver sol( xnf, num_vars, opts );

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
    s.end = std::chrono::high_resolution_clock::now();
    if(opts.verb>0) s.print_final();

    if(opts.sol_count>1) std::cout << "c solutions found: "+std::to_string( std::count_if(s.sols.begin(),s.sols.end(), [](const vec<bool>& sol){ return sol.size()>0; } ) ) << std::endl;
    else s.print_sol();

    if(opts.verb >= 120) { std::cout << opts.to_str() << std::endl; }
    
    if(opts.verb > 0 && s.is_sat()) { //check sol!
        if(check_sols(xnf, s.sols)) {
            std::cout << "c solution(s) verified" << std::endl;
            return 10;
        } else {
            std::cout << "c solution(s) INCORRECT!" << std::endl;
            return 1;
        }
    } else {
        return s.cancelled.load() ? 0 : (s.is_sat() ? 10 :  20);
    }
}

stats solve(const vec< vec<lineral> >& xnf, const var_t num_vars, const options& opts) {
    stats s; solve(xnf, num_vars, opts, s); return s;
}

//perform one gcp run
std::string gcp_only(const vec< vec<lineral> >& xnf, const var_t num_vars, const options& opts, stats& s) {
    //time comp, start
    s.begin = std::chrono::high_resolution_clock::now();

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
                do { sol.GCP(s); } while( sol.initial_GE_processing(s) || sol.initial_IG_processing(s) );
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
        do { sol.GCP(s); } while( sol.initial_GE_processing(s) || sol.initial_IG_processing(s) );
        out = sol.to_xnf_str();
    };
    
    //print stats
    s.end = std::chrono::high_resolution_clock::now();
    if(opts.verb>0) s.print_gcp_info();
    return out;
}


bool check_sol(const vec< vec<lineral> >& clss, const vec<bool>& sol) {
    return std::all_of( clss.begin(), clss.end(), /* all clauses need to be satisfied */
                    [&sol] (vec<lineral> cls) -> bool { 
                        return std::any_of(cls.begin(), cls.end(), [&sol](lineral l) { return l.eval(sol); } ); /* at least one lit of clause must be satisfied */
                        }
                    );
}

bool check_sols(const vec< vec<lineral> >& clss, const list<vec<bool>>& sols) {
    return std::all_of( sols.begin(), sols.end(), [&clss,&sols](const vec<bool>& sol){ return sol.size()==0 || check_sol(clss, sol); } );
}