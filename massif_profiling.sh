#/bin/bash

echo "profiling xnf_solver with valgrind-massif"

#running valgrind tools
#valgrind --tool=massif --time-unit=B --stacks=yes build/2xnf_solver ../benchmarks/instances/2xnfs/rand/rand-10-20.xnf
valgrind --tool=massif --time-unit=B --stacks=yes build/2xnf_solver ../benchmarks/instances/2xnfs/bivium/bivium-t200-g40.xnf -t 30
#valgrind --tool=massif --stacks=yes build/2xnf_solver ../benchmarks/instances/2xnfs/rand/rand-20-60.xnf

#ms_print massif.out.*
massif-visualizer massif.out.*
rm massif.out.*
