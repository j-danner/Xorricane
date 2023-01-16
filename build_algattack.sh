#!/bin/bash

#set custom gcc-11 install
export CXX=~/gcc11/bin/g++
export CC=~/gcc11/bin/gcc

rm -r build
mkdir build
rm -r _build

cmake -DCMAKE_BUILD_TYPE=Release -S . -B _build
cd _build
VERBOSE=1 make xnf_cdcl_solver testing bench -j8 --no-print-directory
mv xnf_cdcl_solver ../build/xnf_cdcl_solver
mv testing ../build/testing
mv bench ../build/bench
cd ..
rm -r _build
