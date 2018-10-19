extern crate id_tree;
extern crate ndarray;
extern crate regex;

use lex::{MetaIter, Token};
use std::io::Read;

// import macros before anything else
pub mod macros;
// ...
pub mod lang;
pub mod lex;
pub mod syn;
pub mod tree_util;

/// Fancy tokens printer.
pub fn print_tokens<'a, T: Token<'a>, I: MetaIter<'a, T>>(tokens: I) {
    println!("Tokens:");
    for (i, t) in tokens.enumerate() {
        match t {
            Ok(meta) => println!("#{:02}: {}", i + 1, meta.token.describe()),
            Err(error) => {
                println!("{}", error);
            }
        }
    }
}

fn main() {
    let mut stdin = std::io::stdin();
    let mut source = String::new();
    stdin.read_to_string(&mut source).ok();

    let syntax = syn::ebnf::Parser::parse(&source, "<stdin>");
    eprintln!("syntax = {:#?}", syntax);

    match syntax {
        Ok(mut syntax) => {
            syntax.ebnf_to_bnf();
            eprintln!("{}", syntax);
        }
        Err(error) => {
            eprintln!("{}", error);
        }
    }
}
