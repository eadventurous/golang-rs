extern crate id_tree;
extern crate ndarray;
extern crate regex;

use lex::{MetaIter, Token};
use std::io::Read;

pub mod lang;
pub mod lex;
pub mod syn;


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

    let lexer = lang::golang::make_lexer();
    let tokens = lexer.into_tokens(&source);
    let tokens = lang::golang::drop_comments(tokens);
    let tokens = lang::golang::necessary_semicolon(tokens);
    print_tokens(tokens);
}
