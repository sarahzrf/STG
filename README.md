This is a compiler for a tiny subset of Haskell into LLVM IR, based vaguely on
the STG machine. The implementation implicitly assumes a 64-bit target
platform; it has no typechecker, and will produce broken programs if fed
mis-typed input; it supports I/O only by writing a function [Int] -> [Int] that
consumes input bytes and returns output bytes; and it has no proper error
messages for input that uses unsupported constructs. That said, it can compile
a simple strict-tail-recursive `sumtorial 10000000` into a binary that runs in
about 0.23s on my machine, which is actually *faster* than an equivalent
program compiled by GHC without optimizations (of course, *with* optimizations,
GHC beats it by an order of magnitude). It also has a mostly-working garbage
collector.

The output is only known to work with LLVM 5, and definitely won't be
accepted by 3, at least.
