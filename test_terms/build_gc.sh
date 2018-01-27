#!/usr/bin/env bash
set -e

s_out="$1"
out="$2"
shift 2

sed -e 's/) {/) gc "statepoint-example" {/' \
    -e '/musttail/ s/$/ "gc-leaf-function"/' \
    | opt -O1 -rewrite-statepoints-for-gc -O2 -S | llc > "$s_out"

gcc -g -Wall -Wpedantic ~/codes/haskell/STG/src/*.c "$s_out" -O0 -o "$out"

