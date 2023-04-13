# A PDDL parser for Python

This repository provides a simple parser for the Planning Domain
Definition Language (PDDL), using the [pyparsing][1] library.

It implements the BNF of PDDL 3.1 as described in:

> Daniel L. Kovacs: Complete BNF description of PDDL 3.1 (completely
> corrected), 2011.

It is assumed that all keywords and identifiers are caseless (so
`:strips` is identified with `:STRIPS`, and `move-block` with
`MOVE-BLOCK`).

The two functions for parsing domain and problem files return an
abstract syntax tree (AST) in the form of a dictionary.

The `examples` directory contains a few example files from standard
benchmarks. To see their ASTs, run

    $ pytest -s pddl_parser.py

[1]: https://pypi.org/project/pyparsing/
