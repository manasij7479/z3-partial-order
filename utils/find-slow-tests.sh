#!/bin/bash
num_tests=100
num_vars=100
num_pos=300
num_neg=100

if [ ! -d "tests" ]; then
  rm -rf outs
  python generate-many.py $num_tests $num_vars $num_pos $num_neg
fi

./run-all-and-sort.sh outs ../z3/buildr/z3
cat result | more
