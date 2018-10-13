extern crate regex;
extern crate ndarray;
extern crate id_tree;

pub mod lang;
pub mod lex;
pub mod syn;

use lex::{Lexer, Token};
use syn::bnf;
use syn::predictive_parser;

use std::io::Read;

/// Little helper for tests.
pub fn token<'a, T: Token<'a>>(x: Option<Result<(&'a str, T), ()>>) -> T {
    x.unwrap().unwrap().1
}


pub fn engine<'a, T>(lexer: &Lexer<'a, T>, mut source: &'a str) -> Result<Vec<T>, Vec<T>>
    where T: Token<'a>
{
    let mut tokens = vec![];

    while let Some(result) = lexer.next(source) {
        match result {
            Ok((rest, token)) => {
                // println!("{} {} {:?}", source.len(), source, token);
                source = rest;
                tokens.push(token);
            }
            Err(_) => return Err(tokens)
        }
    }
    Ok(tokens)
}

pub fn print_tokens<'a, T: Token<'a>>(tokens: Vec<T>) {
    println!("Tokens:");
    for (i, t) in tokens.iter().enumerate() {
        println!("#{:02}: {:?}", i + 1, t);
    }
}


fn main() {
    let mut stdin = std::io::stdin();
    let mut source = String::new();
    stdin.read_to_string(&mut source).ok();

    let lexer = lang::golang::make_lexer();
    match engine(&lexer, &source) {
        Ok(tokens) => print_tokens(tokens),
        Err(tokens) => {
            print_tokens(tokens);
            println!("ERROR");
        }
    }
}
