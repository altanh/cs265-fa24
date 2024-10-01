#!/bin/bash

# ./run-test.sh test-name input.bril
test_name=$1
input_file=$2

cat $input_file | bril2json | cargo test $test_name -- --nocapture
