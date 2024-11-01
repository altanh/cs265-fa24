#!/bin/bash

file=$1
shift 1

cat $file | bril2json | RUST_BACKTRACE=1 cargo run -- $@ | bril2txt
