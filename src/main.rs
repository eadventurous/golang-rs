extern crate regex;

pub mod lang;
pub mod lex;

use lex::{Token, Tokens};

use std::io::Read;

/// Little helper for tests.
pub fn token<'a, T: Token<'a>>(x: Option<Result<(&'a str, T), ()>>) -> T {
    x.unwrap().unwrap().1
}

/// Fancy tokens printer.
pub fn print_tokens<'a, T: Token<'a>>(tokens: Tokens<'a, T>) {
    println!("Tokens:");
    for (i, t) in tokens.enumerate() {
        match t {
            Ok(token) => println!("#{:02}: {}", i + 1, token.describe()),
            Err(_rest) => {
                println!("ERROR")

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
    print_tokens(tokens);
}
