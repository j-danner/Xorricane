#!/bin/bash
trap "rm -rf _build" EXIT

mkdir _build
mkdir build

set -e #exit on error -- cleanup is then done by trap

cmake -DCMAKE_BUILD_TYPE=Release -S . -B _build
VERBOSE=1 make -C _build xnf_cdcl_solver testing bench -j10 --no-print-directory

rm -rf build
mkdir build

mv _build/xnf_cdcl_solver build/xnf_cdcl_solver
mv _build/testing         build/testing
mv _build/bench           build/bench
