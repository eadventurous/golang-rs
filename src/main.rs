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

fn read(now_what: &str) -> String {
    println!("Reading {} from stdin...", now_what);
    let mut stdin = std::io::stdin();
    let mut string = String::new();
    stdin.read_to_string(&mut string).ok();
    string
}

fn main() {
    let source = read("Go code");
    let _ = syn::golang::build_tree(&source, "<stdin>".into(), true);
}


#[cfg(none)]
fn main_2() {
    const FILENAME: &str = "<stdin>";

    let source = read("syntax");
    let syntax = syn::ebnf::Parser::new(&source, FILENAME.into()).parse();
    println!("syntax = {:#?}", syntax);

    match syntax {
        Ok(ref syntax) => {
            let mut left = syntax.clone();
            left.expand_ebnf(syn::ebnf::Recursion::Left);
            let bnf = left.into_bnf().unwrap();
            println!("Left {}", left);
            println!("Left BNF {:#?}", bnf);

            let mut right = syntax.clone();
            right.expand_ebnf(syn::ebnf::Recursion::Right);
            println!("Right {}", right);

            let source = read("source code");
            let root_symbol = bnf.rules[0].name;

            let lexer = lang::golang::make_lexer();
            let tokens = lexer.into_tokens(&source, FILENAME.into());

            match syn::predictive_parser::parse_tokens(&bnf, root_symbol, tokens) {
                Ok(tree) => {
                    println!("{}", tree_util::TreeFmt(&tree));
                }
                Err(e) => {
                    println!("{}", e);
                }
            }
        }
        Err(error) => {
            println!("{}", error);
        }
    }
}
