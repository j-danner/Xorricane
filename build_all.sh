#!/bin/bash

rm -r build
mkdir build
rm -r _build

cmake -DCMAKE_BUILD_TYPE=Release -S . -B _build
cd _build
VERBOSE=1 make xnf_cdcl_solver testing bench -j4 --no-print-directory
mv xnf_cdcl_solver ../build/xnf_cdcl_solver
mv testing ../build/testing
mv bench ../build/bench
cd ..
rm -r _build

