#!/bin/bash
# Reads configs from a file
# num_vars num_clauses neg_prob clause_size name
make
make -C ../ release
mkdir -p tests
cd tests
rm *
touch result
ulimit -t 60
while read p; do
  filename=`echo $p | awk '{print $5}'`
  # echo $p
  echo $filename
  ../gen-targetted-clauses $p
  t=`(time ../../z3.out.release $filename) 2>&1 >/dev/null | grep 'real' | awk '{print $2}'`
  echo "PO: " $t $filename >> result
  cp $filename po-$filename

  ../gen-targetted-clauses $p 1
  t=`(time ../../z3.out.release $filename) 2>&1 >/dev/null | grep 'real' | awk '{print $2}'`
  echo "IDL: " $t $filename >> result
done < ../$1