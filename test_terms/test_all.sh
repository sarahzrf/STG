#!/usr/bin/env bash
set -e

filesdir="$(dirname $(readlink -f ${BASH_SOURCE[0]}))"

pairs=()
bins=()
for test_file in "$filesdir/"test*.txt; do
    pairs[${#pairs[@]}]="$test_file"
    bin="$(mktemp)"
    bins[${#bins[@]}]="$bin"
    pairs[${#pairs[@]}]="$bin"
done

"$filesdir"/compile.sh "${pairs[@]}"
for bin in "${bins[@]}"; do
    time echo hello | "$bin"
    echo -ne "\n\n"
done

