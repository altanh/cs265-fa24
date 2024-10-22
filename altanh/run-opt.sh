#!/bin/bash

file=$1

cat $1 | bril2json | cargo run -- giga | bril2txt
