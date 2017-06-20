#!/bin/bash

make
make -C ..

(for file in tests/*; do ./po-test $file; done) > /tmp/test
(for file in outs/*; do ../z3.out $file; done) > /tmp/out

diff /tmp/test /tmp/out