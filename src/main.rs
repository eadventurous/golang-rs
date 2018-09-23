extern crate regex;

pub mod lang;
pub mod lex;

use lex::{Lexer, Token};

use std::io::Read;

/// Little helper for tests.
pub fn token<'a, T: Token<'a>>(x: Option<Result<(&'a str, T), ()>>) -> T {
    x.unwrap().unwrap().1
}

/// Engine which uses lexer to split source code into lexemes.
///
/// This engine is just an example of how processing whole file might be
/// implemented. While it is powerful enough to handle any source file,
/// it has some limitations: for example, it does not provide information
/// about location and span of generated tokens.
///
/// # Returns
///
/// Vector of all tokens in source code on success, or
/// vector of all tokens up to the point of failure on parse error.
pub fn engine<'a, T>(lexer: &Lexer<'a, T>, mut source: &'a str) -> Result<Vec<T>, Vec<T>>
    where T: Token<'a>
{
    let mut tokens = vec![];

    while let Some(result) = lexer.next(source) {
        match result {
            Ok((rest, token)) => {
                source = rest;
                tokens.push(token);
            }
            Err(_) => return Err(tokens)
        }
    }
    Ok(tokens)
}

/// Fancy tokens printer.
pub fn print_tokens<'a, T: Token<'a>>(tokens: Vec<T>) {
    println!("Tokens:");
    for (i, t) in tokens.iter().enumerate() {
        println!("#{:02}: {}", i + 1, t.describe());
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
