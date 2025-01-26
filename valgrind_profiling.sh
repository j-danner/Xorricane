#/bin/bash

echo "profiling xnf_solver"

#running valgrind tools
#valgrind --tool=callgrind --dump-instr=yes --simulate-cache=yes --collect-jumps=yes build/xorricane ../benchmarks/instances/2xnfs/rand/rand-20-60.xnf -t 30
#valgrind --tool=callgrind --dump-instr=yes build/xorricane ../benchmarks/instances/2xnfs/rand/rand-30-90.xnf -ca dpll -t 60 -dh lwl
#valgrind --tool=callgrind --dump-instr=yes build/xorricane ../benchmarks/instances/2xnfs/matrix_multiplication/MM-22.xnf -ca 1uip -t 60
#valgrind --tool=callgrind --dump-instr=yes build/xorricane ../benchmarks/instances/2xnfs/mq/toyexamples/ToyExample-type1-n20-seed0.xnf -ca dpll -t 60
#valgrind --tool=callgrind --dump-instr=yes build/xorricane ../benchmarks/instances/2xnfs/mq/toyexamples/ToyExample-type1-n20-seed0.xnf -ca 1uip -t 60 -cm
#valgrind --tool=callgrind --dump-instr=yes build/xorricane ../benchmarks/instances/2xnfs/test35.xnf -ca 1uip -t 60
#valgrind --tool=callgrind --dump-instr=yes build/xorricane ../benchmarks/instances/2xnfs/mq/toyexamples/ToyExample-type1-n20-seed0.xnf -ca 1uip -rh luby -dh vsids -t 60
#valgrind --tool=callgrind --dump-instr=yes build/xorricane ../benchmarks/instances/2xnfs/mq/toyexamples/ToyExample-type1-n20-seed0.xnf -ca 1uip -rh luby -dh vsids -pp no -t 60
#valgrind --tool=callgrind build/xorricane ../benchmarks/instances/2xnfs/bivium/bivium-t150-g40.xnf -t 30 -ca 1uip -rh luby -la 30
#valgrind --tool=callgrind build/xorricane ../benchmarks/instances/2xnfs/rand/rand-20-60.xnf -dh vsids -ca 1uip -rh luby
#valgrind --tool=callgrind build/xorricane ../benchmarks/instances/2xnfs/rand/rand-20-60.xnf -dh vsids -ca 1uip -rh no -t 30 -cm
#valgrind --tool=callgrind --dump-instr=yes --simulate-cache=yes --collect-jumps=yes build/xorricane ../benchmarks/bench_instances/bivium/tmp04_lvzwb.xnf -ca 1uip -po save -ip nbu -rh luby -dh vsids -no-lgj -t 60
valgrind --tool=callgrind --dump-instr=yes --simulate-cache=yes --collect-jumps=yes build/xorricane ../benchmarks/bench_instances/rand_qp/tmpt9coke09.xnf -ca 1uip -po save -pp no -ip no -rh luby -dh vsids -t 60
#valgrind --tool=callgrind --dump-instr=yes build/xorricane ../benchmarks/generate_instances/bivium/bivium-t354-g55.2xnf -ca 1uip -po save -ip nbu -rh luby -dh vsids

kcachegrind callgrind.out.*
rm callgrind.out.*

#valgrind --tool=cachegrind build/xorricane ../benchmarks/instances/2xnfs/rand/rand-20-60.xnf -dh lex -ca 1uip -rh luby -t 30
#
#cg_annotate cachegrind.out.*
#rm cachegrind.out.*
