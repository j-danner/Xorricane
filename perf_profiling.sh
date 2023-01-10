#/bin/bash

echo "profiling xnf_solver with perf (from linux-tools)"

#run perf record
perf record -g build/2xnf_solver ../benchmarks/instances/2xnfs/rand/rand-20-60.xnf

#inspect result
sudo perf report

rm perf.data*
