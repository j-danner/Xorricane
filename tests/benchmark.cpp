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

//BENCHMARK_CAPTURE(BM_dpll_solve, rand-20-60, "../../benchmarks/instances/2xnfs/rand/rand-20-60.xnf")->Unit(benchmark::kMillisecond)->Repetitions(10)->DisplayAggregatesOnly(true);
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


int xlit_performance(var_t n, long k) {
    //compute k random xlit additions in n vars
    vec< xlit > xlits;
    xlits.reserve(2*k);

    vec<var_t> xlit_set;
    srand((unsigned)time(NULL));
    for(var_t j=0; j<2*k; j++) {
        for (var_t i=0; i < n; i++){
            if(rand() % 2) xlit_set.push_back(i);
        }
        xlits.push_back( xlit(xlit_set) );
        xlit_set.clear();
    }

    //performance analysis:
    auto start = std::chrono::steady_clock::now();
    vec<xlit> sums;
    sums.reserve(k);

    for (int i = 0; i < k; i++)
    {
        sums[i] = xlits[2*i] + xlits[2*i+1];
    }
    auto end = std::chrono::steady_clock::now();

    std::cout << k << " additions of random xlits in " << n << " inds took " << std::chrono::duration_cast<std::chrono::seconds> (end - start).count() << "s." << std::endl;

    return 1;
}


BENCHMARK_MAIN();