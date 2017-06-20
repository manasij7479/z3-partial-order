#!/bin/bash

make
make -C ..

#python generate-many.py 10 100 90 30

(for file in tests/*; do ./po-test $file; done) > /tmp/test
(for file in outs/*; do ../z3.out $file; done) > /tmp/out

pr -m -t /tmp/test /tmp/out

diff /tmp/test /tmp/out