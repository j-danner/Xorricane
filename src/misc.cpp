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
        std::cout << BOLD(RED("!!! INTERRUPTED !!!")) << std::endl;
        std::cout << "c " << std::endl;
        s.cancelled.store( true ); //make sure the main solve call ends in next iteration!
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

    //print sols
    if(opts.sol_count>1) {
        std::cout << "c " << GRAY("solutions found: "+std::to_string( std::count_if(s.sols.begin(),s.sols.end(), [](const vec<bool>& sol){ return sol.size()>0; } ) )) << std::endl;
    } else {
        s.print_sol(opts.verb>0);
    }

    if(opts.verb >= 120) { std::cout << opts.to_str() << std::endl; }
    
    auto ret_value = 0;
    if(opts.verb > 0 && s.is_sat()) { //check sol!
        if(check_sols(xnf, s.sols)) {
            std::cout << "c " << GREEN("solution(s) verified") << std::endl;
            ret_value = 10;
        } else {
            std::cout << "c " << BOLD(RED("solution(s) INCORRECT!")) << std::endl;
            ret_value = 1;
        }
        std::cout << "c " << std::endl;
    } else {
        ret_value = s.cancelled.load() ? 0 : (s.is_sat() ? 10 :  20);
    }

    //print stats
    s.end = std::chrono::high_resolution_clock::now();
    if(opts.verb>0) s.print_final();

    return ret_value;
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
                sol.GCP_inprocess(s);
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
        sol.GCP_inprocess(s);
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