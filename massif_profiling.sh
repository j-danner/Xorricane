#/bin/bash

echo "profiling xnf_solver with valgrind-massif"

#running valgrind tools
valgrind --tool=massif --time-unit=B --stacks=yes build/xnf_cdcl_solver ../benchmarks/instances/2xnfs/matrix_multiplication/MM-22.xnf -ca no -t 60 -dh lwl

#ms_print massif.out.*
massif-visualizer massif.out.*
rm massif.out.*
