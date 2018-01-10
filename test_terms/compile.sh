#!/usr/bin/env bash
set -e

filesdir="$(dirname $(readlink -f ${BASH_SOURCE[0]}))"
bump="$filesdir/bump.ll"
compiler="$filesdir/../dist/build/STG/STG"

[[ -n "$1" && -n "$2" ]]
file="$1"
ll="$(mktemp --suffix=.ll)"

cabal build
while [[ $# -ge 2 ]]; do
    file="$1"
    ll="$(mktemp --suffix=.ll)"
    "$compiler" < "$file" > "$ll"
    opt -q "$ll"
    clang -Wno-override-module -Qunused-arguments -O3 "$bump" "$ll" -o "$2"
    shift 2
done

