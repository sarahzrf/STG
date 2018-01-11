#!/usr/bin/env bash
set -e

filesdir="$(dirname $(readlink -f ${BASH_SOURCE[0]}))"
bump="$filesdir/bump.ll"
compiler="$filesdir/../dist/build/STG/STG"

cabal build -v0
ll="$(mktemp --suffix=.ll)"
while [[ $# -ge 2 ]]; do
    file="$1"
    ll="$(mktemp --suffix=.ll)"
    "$compiler" < "$file" > "$ll"
    opt -verify "$ll" > /dev/null
    clang -Wno-override-module -Qunused-arguments -O3 "$bump" "$ll" -o "$2"
    shift 2
done

