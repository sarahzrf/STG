#!/usr/bin/env bash
set -e

filesdir="$(dirname $(readlink -f ${BASH_SOURCE[0]}))"
bump="$filesdir/bump.ll"

[[ -n "$1" && -n "$2" ]]
file="$1"
ll="$(mktemp --suffix=.ll)"

cabal run -v0 < "$file" > "$ll"
opt -q "$ll"
clang -Wno-override-module -Qunused-arguments -O3 "$bump" "$ll" -o "$2"

