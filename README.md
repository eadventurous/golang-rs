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
To build and run the program from the sources execute the following command in bash or powershell while in the main folder:

    cargo run <in.txt >out.txt

This will read code from *in.txt* and write tokens into *out.txt*.

If the given file had correct tokens the out.txt will look like:

    Tokens:
    #01: Comment(" You can edit this code!\r")
    #02: Comment(" Click here and start typing.\r")
    #03: Keyword(Package)
    #04: Ident("main")
    #05: Keyword(Import)
    #06: Literal(InterpretedString("fmt"))
    ...
With each token on a new line. Ending with the last token in the file.

Yet if the lexer encounters an incorrect token, it will print `ERROR` in its place and stop parsing. For example:

    Tokens:
    #01: Comment(" You can edit this code!\r")
    #02: Comment(" Click here and start typing.\r")
    #03: Keyword(Package)
    #04: Ident("main")
    ERROR

### Testing
To run the tests execute the following command in bash or powershell:

    cargo test

### References
1) [Go tokens](https://golang.org/src/go/token/token.go) we used their naming convention for token definitions.
2) [Go specs](https://golang.org/ref/spec) were used by us for constructing regular expressions for token recognition.
