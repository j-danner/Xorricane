#!/bin/bash

#set custom gcc-11 install
export CXX=~/gcc11/bin/g++
export CC=~/gcc11/bin/gcc

rm -r build
mkdir build
rm -r _build

cmake -DCMAKE_BUILD_TYPE=Release -DUSE_TRIV_XL_W=OFF -DUSE_LAZY_XL_W=ON -DUSE_PQ_XL_W=OFF -DUSE_INCR_XL_W=OFF -S . -B _build
cd _build
VERBOSE=1 make xnf_cdcl_solver testing bench -j8 --no-print-directory
mv xnf_cdcl_solver ../build/xnf_cdcl_solver_lazy
mv testing ../build/testing_lazy
mv bench ../build/bench_lazy
cd ..
#rm -r _build

cmake -DCMAKE_BUILD_TYPE=Release -DUSE_TRIV_XL_W=OFF -DUSE_LAZY_XL_W=OFF -DUSE_PQ_XL_W=ON -DUSE_INCR_XL_W=OFF -S . -B _build
cd _build
VERBOSE=1 make xnf_cdcl_solver testing bench -j8 --no-print-directory
mv xnf_cdcl_solver ../build/xnf_cdcl_solver_pq
mv testing ../build/testing_pq
mv bench ../build/bench_pq
cd ..
#rm -r _build

cmake -DCMAKE_BUILD_TYPE=Release -DUSE_TRIV_XL_W=OFF -DUSE_LAZY_XL_W=OFF -DUSE_PQ_XL_W=OFF -DUSE_INCR_XL_W=ON -S . -B _build
cd _build
VERBOSE=1 make xnf_cdcl_solver testing bench -j8 --no-print-directory
mv xnf_cdcl_solver ../build/xnf_cdcl_solver_incr
mv testing ../build/testing_incr
mv bench ../build/bench_incr
cd ..
#rm -r _build

cmake -DCMAKE_BUILD_TYPE=Release -DUSE_TRIV_XL_W=ON -DUSE_LAZY_XL_W=OFF -DUSE_PQ_XL_W=OFF -DUSE_INCR_XL_W=OFF -S . -B _build
cd _build
VERBOSE=1 make xnf_cdcl_solver testing bench -j8 --no-print-directory
mv xnf_cdcl_solver ../build/xnf_cdcl_solver
mv testing ../build/testing
mv bench ../build/bench
cd ..
rm -r _build
