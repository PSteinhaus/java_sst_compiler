# JavaSST compiler in Rust

This repository holds a small compiler for a tiny, educational, Java-like language called JavaSST.

It reads in source files and compiles them down to Java bytecode (version 49.0).

Additionally, the abstract syntax tree (AST) that the code generation is based on can be displayed when the program
is called with the `--dot-rep` flag:

![ast](https://user-images.githubusercontent.com/40324631/152229371-38a8095a-65f4-4c14-9d19-97dadcd95b6f.svg)
