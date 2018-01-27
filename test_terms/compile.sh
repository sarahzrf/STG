#!/usr/bin/env bash
set -e

filesdir="$(dirname $(readlink -f ${BASH_SOURCE[0]}))"
gc=("$filesdir"/../src/*.c)
compiler="$filesdir/../dist/build/STG/STG"

cabal build -v0
ll="$(mktemp --suffix=.ll)"
while [[ $# -ge 2 ]]; do
    file="$1"
    s="$(mktemp --suffix=.s)"
    "$compiler" < "$file" | sed \
        -e 's/) {/) gc "statepoint-example" {/' \
        -e '/musttail/ s/$/ "gc-leaf-function"/' \
        | opt -O1 -rewrite-statepoints-for-gc -O2 -S | llc > "$s"
    clang -Wall -Wpedantic -O3 "${gc[@]}" "$s" -o "$2"
    shift 2
done

