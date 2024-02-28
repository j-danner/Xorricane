//file to test implementation of xcls
#include "../src/solver.hpp"

#include <benchmark/benchmark.h>

#define concat(first, second) first second


static void BM_dpll_solve(benchmark::State& state, std::string fname) {
    for (auto _ : state) {
        auto clss = parse_file(fname);
        auto slvr = solver(clss);
        stats s = slvr.dpll_solve();
    }
}

static void BM_cdcl_solve(benchmark::State& state, std::string fname) {
    for (auto _ : state) {
        auto clss = parse_file(fname);
        auto slvr = solver(clss);
        stats s = slvr.solve();
    }
}

static void BM_cdcl_solve_cm(benchmark::State& state, std::string fname) {
    options opt;
    opt.cm = true;
    opt.eq = true;
    opt.rst = restart_opt::luby;
    opt.ip = initial_prop_opt::nbu;
    for (auto _ : state) {
        auto clss = parse_file(fname);
        auto slvr = solver(clss, opt);
        stats s = slvr.solve();
    }
}

BENCHMARK_CAPTURE(BM_dpll_solve, rand-20-60, concat(BENCH_FILES, "/instances/2xnfs/rand/rand-20-60.xnf") )->Unit(benchmark::kMillisecond)->MinTime(2);
BENCHMARK_CAPTURE(BM_dpll_solve, rand-10-20, concat(BENCH_FILES, "/instances/2xnfs/rand/rand-10-20.xnf") )->Unit(benchmark::kMillisecond)->MinTime(2);
BENCHMARK_CAPTURE(BM_dpll_solve, rand-5-10,  concat(BENCH_FILES, "/instances/2xnfs/rand/rand-5-10.xnf") )->Unit(benchmark::kMillisecond)->MinTime(2);
BENCHMARK_CAPTURE(BM_dpll_solve, mq-toyexample-type1-n15,  concat(BENCH_FILES, "/instances/2xnfs/mq/toyexamples/ToyExample-type1-n15-seed0.xnf") )->Unit(benchmark::kMillisecond)->MinTime(2);
BENCHMARK_CAPTURE(BM_dpll_solve, mq-toyexample-type1-n15,  concat(BENCH_FILES, "/instances/2xnfs/mq/toyexamples/ToyExample-type1-n15-seed1.xnf") )->Unit(benchmark::kMillisecond)->MinTime(2);
BENCHMARK_CAPTURE(BM_dpll_solve, mq-toyexample-type1-n15,  concat(BENCH_FILES, "/instances/2xnfs/mq/toyexamples/ToyExample-type1-n15-seed2.xnf") )->Unit(benchmark::kMillisecond)->MinTime(2);
BENCHMARK_CAPTURE(BM_dpll_solve, mq-toyexample-type1-n15,  concat(BENCH_FILES, "/instances/2xnfs/mq/toyexamples/ToyExample-type1-n15-seed3.xnf") )->Unit(benchmark::kMillisecond)->MinTime(2);
BENCHMARK_CAPTURE(BM_dpll_solve, mq-toyexample-type1-n15,  concat(BENCH_FILES, "/instances/2xnfs/mq/toyexamples/ToyExample-type1-n15-seed4.xnf") )->Unit(benchmark::kMillisecond)->MinTime(2);

BENCHMARK_CAPTURE(BM_cdcl_solve, rand-20-60, concat(BENCH_FILES, "/instances/2xnfs/rand/rand-20-60.xnf") )->Unit(benchmark::kMillisecond)->MinTime(2);
BENCHMARK_CAPTURE(BM_cdcl_solve, rand-10-20, concat(BENCH_FILES, "/instances/2xnfs/rand/rand-10-20.xnf") )->Unit(benchmark::kMillisecond)->MinTime(2);
BENCHMARK_CAPTURE(BM_cdcl_solve, rand-5-10,  concat(BENCH_FILES, "/instances/2xnfs/rand/rand-5-10.xnf") )->Unit(benchmark::kMillisecond)->MinTime(2);
BENCHMARK_CAPTURE(BM_cdcl_solve, mq-toyexample-type1-n15,  concat(BENCH_FILES, "/instances/2xnfs/mq/toyexamples/ToyExample-type1-n15-seed0.xnf") )->Unit(benchmark::kMillisecond)->MinTime(2);
BENCHMARK_CAPTURE(BM_cdcl_solve, mq-toyexample-type1-n15,  concat(BENCH_FILES, "/instances/2xnfs/mq/toyexamples/ToyExample-type1-n15-seed1.xnf") )->Unit(benchmark::kMillisecond)->MinTime(2);
BENCHMARK_CAPTURE(BM_cdcl_solve, mq-toyexample-type1-n15,  concat(BENCH_FILES, "/instances/2xnfs/mq/toyexamples/ToyExample-type1-n15-seed2.xnf") )->Unit(benchmark::kMillisecond)->MinTime(2);
BENCHMARK_CAPTURE(BM_cdcl_solve, mq-toyexample-type1-n15,  concat(BENCH_FILES, "/instances/2xnfs/mq/toyexamples/ToyExample-type1-n15-seed3.xnf") )->Unit(benchmark::kMillisecond)->MinTime(2);
BENCHMARK_CAPTURE(BM_cdcl_solve, mq-toyexample-type1-n15,  concat(BENCH_FILES, "/instances/2xnfs/mq/toyexamples/ToyExample-type1-n15-seed4.xnf") )->Unit(benchmark::kMillisecond)->MinTime(2);

//BENCHMARK_CAPTURE(BM_cdcl_solve_cm, rand-20-60, concat(BENCH_FILES, "/instances/2xnfs/rand/rand-20-60.xnf") )->Unit(benchmark::kMillisecond)->MinTime(2);
//BENCHMARK_CAPTURE(BM_cdcl_solve_cm, rand-10-20, concat(BENCH_FILES, "/instances/2xnfs/rand/rand-10-20.xnf") )->Unit(benchmark::kMillisecond)->MinTime(2);
//BENCHMARK_CAPTURE(BM_cdcl_solve_cm, rand-5-10,  concat(BENCH_FILES, "/instances/2xnfs/rand/rand-5-10.xnf") )->Unit(benchmark::kMillisecond)->MinTime(2);
//BENCHMARK_CAPTURE(BM_cdcl_solve_cm, mq-toyexample-type1-n15,  concat(BENCH_FILES, "/instances/2xnfs/mq/toyexamples/ToyExample-type1-n15-seed0.xnf") )->Unit(benchmark::kMillisecond)->MinTime(2);
//BENCHMARK_CAPTURE(BM_cdcl_solve_cm, mq-toyexample-type1-n15,  concat(BENCH_FILES, "/instances/2xnfs/mq/toyexamples/ToyExample-type1-n15-seed1.xnf") )->Unit(benchmark::kMillisecond)->MinTime(2);
//BENCHMARK_CAPTURE(BM_cdcl_solve_cm, mq-toyexample-type1-n15,  concat(BENCH_FILES, "/instances/2xnfs/mq/toyexamples/ToyExample-type1-n15-seed2.xnf") )->Unit(benchmark::kMillisecond)->MinTime(2);
//BENCHMARK_CAPTURE(BM_cdcl_solve_cm, mq-toyexample-type1-n15,  concat(BENCH_FILES, "/instances/2xnfs/mq/toyexamples/ToyExample-type1-n15-seed3.xnf") )->Unit(benchmark::kMillisecond)->MinTime(2);
//BENCHMARK_CAPTURE(BM_cdcl_solve_cm, mq-toyexample-type1-n15,  concat(BENCH_FILES, "/instances/2xnfs/mq/toyexamples/ToyExample-type1-n15-seed4.xnf") )->Unit(benchmark::kMillisecond)->MinTime(2);


static void xlit_performance(benchmark::State& state, var_t n, var_t prob, unsigned long k) {
    //compute k random xlit additions in n vars
    vec< xlit > xlits;
    xlits.reserve(2*k);

    vec<var_t> xlit_set;
    xlit_set.reserve(n);
    srand((unsigned) 123456789);
    for(var_t j=0; j<2*k; j++) {
        for (var_t i=0; i < n; i++){
            if( ((var_t) (rand() % 100)) <= prob ) xlit_set.emplace_back(i);
        }
        xlits.emplace_back( xlit(xlit_set) );
        xlit_set.clear();
    }

    //performance analysis:
    vec<xlit> sums;
    sums.reserve(k);

    for (auto _ : state) {
        for (unsigned int i = 0; i < k; i++) {
            sums.emplace_back( xlits[2*i] + xlits[2*i+1] );
        }
    }
}


BENCHMARK_CAPTURE(xlit_performance, xlit-add-n100-d50-k1000, 100, 50, 1000)->Unit(benchmark::kMillisecond)->MinTime(1);
BENCHMARK_CAPTURE(xlit_performance, xlit-add-n1000-d50-k1000, 1000, 50, 1000)->Unit(benchmark::kMillisecond)->MinTime(1);
BENCHMARK_CAPTURE(xlit_performance, xlit-add-n10000-d50-k1000, 10000, 50, 1000)->Unit(benchmark::kMillisecond)->MinTime(1);
BENCHMARK_CAPTURE(xlit_performance, xlit-add-n100-d1-k1000, 100, 1, 1000)->Unit(benchmark::kMillisecond)->MinTime(1);
BENCHMARK_CAPTURE(xlit_performance, xlit-add-n1000-d1-k1000, 1000, 1, 1000)->Unit(benchmark::kMillisecond)->MinTime(1);
BENCHMARK_CAPTURE(xlit_performance, xlit-add-n10000-d1-k1000, 10000, 1, 1000)->Unit(benchmark::kMillisecond)->MinTime(1);

BENCHMARK_MAIN();