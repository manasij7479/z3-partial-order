#!/bin/bash

make
make -C ..

if [ ! -d "tests" ]; then
  python generate-many.py 10 100 90 30
fi
rm -rf /tmp/test /tmp/out
(for file in tests/*; do ./po-test $file; done) > /tmp/test
(for file in outs/*; do ../z3.out $file | head -n 1; done) > /tmp/out

pr -m -t /tmp/test /tmp/out

diff /tmp/test /tmp/out