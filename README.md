rendezvous_hash
===============

[![Crates.io: rendezvous_hash](https://img.shields.io/crates/v/rendezvous_hash.svg)](https://crates.io/crates/rendezvous_hash)
[![Documentation](https://docs.rs/rendezvous_hash/badge.svg)](https://docs.rs/rendezvous_hash)
[![Build Status](https://travis-ci.org/sile/rendezvous_hash.svg?branch=master)](https://travis-ci.org/sile/rendezvous_hash)
[![Code Coverage](https://codecov.io/gh/sile/rendezvous_hash/branch/master/graph/badge.svg)](https://codecov.io/gh/sile/rendezvous_hash/branch/master)
[![License: MIT](https://img.shields.io/badge/license-MIT-blue.svg)](LICENSE)

A Rust implementation of Rendezvous (a.k.a, highest random weight) hashing algorithm.

[Documentation](https://docs.rs/rendezvous_hash)


References
----------

- [Rendezvous hashing (Wikipedia)](https://en.wikipedia.org/wiki/Rendezvous_hashing)
- [Weighted Distributed Hash Tables](https://pdfs.semanticscholar.org/8c55/282dc37d1e3b46b15c2d97f60568ccb9c9cd.pdf)
  - This paper describes an efficient method for calculating consistent hash values for heterogeneous nodes.


An Informal Benchmark
----------------------

```sh
$ cat /proc/cpuinfo  | grep 'model name' | head -1
model name      : Intel(R) Core(TM) i7-6600U CPU @ 2.60GHz

$ uname -a
Linux ubuntu 4.8.0-34-generic #36-Ubuntu SMP Wed Dec 21 17:24:18 UTC 2016 x86_64 x86_64 x86_64 GNU/Linux

$ cargo run --release --example bench -- /usr/share/dict/words --nodes Rust Alef C++ Camlp4 CommonLisp Erlang Haskell Hermes Limbo Napier Napier88 Newsqueak NIL Sather StandardML

WORD COUNT: 99156
NODE COUNT: 15

SELECTED COUNT PER NODE:
- Napier88:     6711
- Haskell:      6607
- StandardML:   6622
- CommonLisp:   6621
- Newsqueak:    6693
- C++:  6605
- Sather:       6495
- Limbo:        6704
- Camlp4:       6536
- Erlang:       6594
- Napier:       6685
- Rust:         6568
- NIL:  6514
- Hermes:       6667
- Alef:         6534

ELAPSED: 84 ms
WORDS PER SECOND: 1177303
```
