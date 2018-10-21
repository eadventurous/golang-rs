HA-2: Lexical Analyzer
======================
General
-------
### Team
* Egor Ivkov
* Ivan Tkachenko

**Target language:** Go

**Implementation language:** Rust

How to run
----------
### Dependencies
* Rust is installed (cargo, rustc)
### Assumptions
For simplicity of use program reads from stdin and writes to stdout.
### Running
To build and run the program from the sources execute the following command in bash or PowerShell while in the main folder:

    cargo run <in.txt >out.txt

This will read code from *in.txt* and write syntax tree into *out.txt*.

This program includes hand-written from scratch LL(1) parser table generator as well as parser for BNF and EBNF syntax definitions. So basically, new grammars may be added at runtime.

However, only little part of Go lang grammar is supported at the moment mostly due to challenging left recursion elimination. Implementing automatic left recursion elimination algorithm was one of our goal, but it's still on the roadmap.

EBNF grammars are supported as described in module-level doc comments of 'src/lang/ebnf.rs'. Automatic expansion of loops, groups and optionals is done before feeding grammar to parser table generator.

Library has limited support for left factorization. It handles obvious cases like `A -> X | X Y Z` with ease but fails to lookup FIRST set for more complex scenarios.

Result of parsing is a tree ADT with String data in nodes. Nodes with non-terminals are displayed with triangle brackets (like some sorts of BNF). Nodes with tokens are formatted as tokens' descriptions which is implementation-defined.

Suppose input is the following Go program:

    package main
    // semicolon is optional.
    import ( "lib/abc"; )
    import M "math"


The following is a sample tree for that program.

    Tree:
    - <Root>
      + <SourceFile>
        * <PackageClause>
          - Package
          - <PackageName>
            + main
        * Operator(Semicolon)
        * <X-auto-3>
          - <ImportDecl>
            + Import
            + <X-auto-5>
              * <ImportSpec>
                - <X-auto-6>
                - <ImportPath>
                  + Literal(InterpretedString("abc"))
          - Operator(Semicolon)
          - <X-auto-3>
        * <X-auto-4>

If source violates syntax/grammar rules, parser behavior is not well-defined. Apparently, it may cause stack overflow, or display nice error message like this:


    Error at <stdin>:2:5
    2   | two word
        |     ^^^^
    3   | tree
        | ^^^^
    Unexpected tokens in at this context: 'word', 'tree'.


### Testing
To run the tests execute the following command in bash or powershell:

    cargo test

### References
1) [Go tokens](https://golang.org/src/go/token/token.go) we used their naming convention for token definitions.
2) [Go specs](https://golang.org/ref/spec) were used by us for constructing regular expressions for token recognition.
