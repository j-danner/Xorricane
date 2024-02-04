#/bin/bash

echo "profiling xnf_solver"

#running valgrind tools
#valgrind --tool=callgrind --dump-instr=yes build/xnf_cdcl_solver ../benchmarks/instances/2xnfs/rand/rand-20-60.xnf
#valgrind --tool=callgrind --dump-instr=yes build/xnf_cdcl_solver ../benchmarks/instances/2xnfs/rand/rand-30-90.xnf -ca dpll -t 60 -dh lwl
#valgrind --tool=callgrind --dump-instr=yes build/xnf_cdcl_solver ../benchmarks/instances/2xnfs/matrix_multiplication/MM-22.xnf -ca dpll -t 60 -dh lwl
#valgrind --tool=callgrind --dump-instr=yes build/xnf_cdcl_solver ../benchmarks/instances/2xnfs/mq/toyexamples/ToyExample-type1-n20-seed0.xnf -ca dpll -t 60
#valgrind --tool=callgrind --dump-instr=yes build/xnf_cdcl_solver ../benchmarks/instances/2xnfs/mq/toyexamples/ToyExample-type1-n20-seed0.xnf -ca 1uip -t 60
#valgrind --tool=callgrind --dump-instr=yes build/xnf_cdcl_solver ../benchmarks/instances/2xnfs/test35.xnf -ca 1uip -t 60
#valgrind --tool=callgrind --dump-instr=yes build/xnf_cdcl_solver ../benchmarks/instances/2xnfs/mq/toyexamples/ToyExample-type1-n20-seed0.xnf -ca 1uip -rh luby -dh vsids -t 60
#valgrind --tool=callgrind build/xnf_cdcl_solver ../benchmarks/instances/2xnfs/bivium/bivium-t150-g40.xnf -t 30
valgrind --tool=callgrind build/xnf_cdcl_solver ../benchmarks/instances/2xnfs/rand/rand-20-60.xnf -dh lex -ca 1uip -rh no
#valgrind --tool=cachegrind build/xnf_cdcl_solver ../benchmarks/instances/2xnfs/rand/rand-20-60.xnf -dh lex -ca no -rh no

kcachegrind callgrind.out.*
rm callgrind.out.*

#cg_annotate cachegrind.out.*
#rm cachegrind.out.*
