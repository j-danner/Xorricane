#!/bin/bash
trap "rm -rf _build" EXIT

mkdir _build
mkdir build

set -e #exit on error -- cleanup is then done by trap

#set custom gcc-13 install
export CXX=~/gcc13/bin/g++
export CC=~/gcc13/bin/gcc

#cmake -DCMAKE_BUILD_TYPE=Debug -S . -B _build
cmake -DCMAKE_BUILD_TYPE=Release -S . -B _build -Wno-dev
VERBOSE=1 make -C _build xorricane testing bench -j8 --no-print-directory

rm -rf build
mkdir build

mv _build/xorricane       build/xorricane
mv _build/testing         build/testing
mv _build/bench           build/bench
