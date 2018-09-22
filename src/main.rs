#![allow(unused_variables)]
#![allow(unused_imports)]
#![allow(dead_code)]

extern crate regex;

pub mod lang;

use lang::{Token, TokenFactory};

use std::io::Read;

use regex::Regex;
use regex::Captures;

pub struct LexerBuilder<'a, T> {
    pairs: Vec<(Regex, Box<TokenFactory<'a, T>>)>,
    skip_whitespaces: fn(&'a str) -> &'a str,
}

impl<'a, T> LexerBuilder<'a, T>
    where T: Token<'a>
{
    pub fn new() -> Self {
        LexerBuilder { pairs: Vec::new(), skip_whitespaces: |x| x }
    }

    /// Shortcut for `add_pair`.
    pub fn add<F>(self, regex: &str, factory: F) -> Self
        where F: Fn(Captures<'a>) -> T + 'static
    {
        assert!(regex.len() > 0);

        let regex = match regex.chars().next().unwrap() {
            '^' => Regex::new(regex),
            _ => Regex::new(&format!("^{}", regex)),
        }.expect("Invalid Regex!");

        let factory = Box::new(factory);

        self.add_pair(regex, factory)
    }

    pub fn add_pair(mut self, regex: Regex, factory: Box<TokenFactory<'a, T>>) -> Self {
        assert_eq!('^', regex.as_str().chars().next().unwrap_or('\0'));
        self.pairs.push((regex, factory));
        self
    }

    /// Set up rule (function) to skip whitespaces before parsing each token.
    pub fn skip_whitespaces(mut self, f: fn(&'a str) -> &'a str) -> Self {
        self.skip_whitespaces = f;
        self
    }

    pub fn build(self) -> Lexer<'a, T> {
        Lexer { pairs: self.pairs, skip_whitespaces: self.skip_whitespaces }
    }
}

pub struct Lexer<'a, T> {
    pairs: Vec<(Regex, Box<TokenFactory<'a, T>>)>,
    skip_whitespaces: fn(&'a str) -> &'a str,
}


impl<'a, T> Lexer<'a, T>
    where T: Token<'a>
{
    /// ```raw
    /// skip_whitespaces(source).is_empty() => None
    /// parse(skip_whitespaces(source)).is_ok() => Some(Ok(rest, token))
    /// parse(skip_whitespaces(source)).is_err() => Some(Err(...))
    /// ```
    pub fn next(&self, source: &'a str) -> Option<Result<(&'a str, T), ()>> {
        // prepare source string
        let source = (self.skip_whitespaces)(source);

        if source.is_empty() { return None; }

        Some(self._next(source))
    }

    fn _next(&self, source: &'a str) -> Result<(&'a str, T), ()> {
        let (len, token) =
            self.pairs.iter()
                // apply regex AND skip mismatches in one shot
                .filter_map(|&(ref regex, ref f)| {
                    regex
                        .captures(source)
                        .map(|c| (c, f))
                }) // type: Iterator<Item=(Captures<'a>, &Box<TokenFactory<T>>)>
                // apply token factory to the captures object
                .map(|(c, f)| (c.get(0).unwrap().as_str().len(), f.token(c)))
                // take the first one that matches
                .next()
                // early return `Err` if empty
                .ok_or(())?;
        let rest = &source[len..];
        Ok((rest, token))
    }
}

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
