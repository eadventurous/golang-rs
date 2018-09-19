#![allow(unused_variables)]
#![allow(unused_imports)]
#![allow(dead_code)]

extern crate regex;

mod lang;

use lang::{Token, TokenFactory};

use regex::Regex;
use regex::Match;

pub struct LexerBuilder<'a, T> {
    pairs: Vec<(Regex, Box<TokenFactory<'a, T>>)>
}

impl<'a, T> LexerBuilder<'a, T>
    where T: Token<'a>
{
    pub fn new() -> Self {
        LexerBuilder { pairs: Vec::new() }
    }

    /// Shortcut for `add_pair`.
    pub fn add<F>(self, regex: &str, factory: F) -> Self
        where F: Fn(Match<'a>) -> T + 'static
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

    pub fn build(self) -> Lexer<'a, T> {
        Lexer { pairs: self.pairs }
    }
}

pub struct Lexer<'a, T> {
    pairs: Vec<(Regex, Box<TokenFactory<'a, T>>)>,
}


impl<'a, T> Lexer<'a, T>
    where T: Token<'a>
{
    pub fn next(&self, source: &'a str) -> Result<(&'a str, T), ()> {
        let (m, token) =
            self.pairs.iter()
                // apply regex AND skip mismatches in one shot
                .filter_map(|&(ref regex, ref f)| {
                    regex
                        .find_at(source, 0)
                        .map(|m| (m, f))
                }) // type: Iterator<Item=(Match<'a>, &Box<TokenFactory<T>>)>
                // apply token factory to the match object
                .map(|(m, ref f)| (m, f.token(m)))
                // take the first one that matches
                .next()
                // early return `Err` if empty
                .ok_or(())?;
        let len = m.as_str().len();
        let rest = &source[len..];
        Ok((rest, token))
    }
}


pub fn engine<'a, T>(lexer: &Lexer<'a, T>, mut source: &'a str) -> Result<Vec<T>, ()>
    where T: Token<'a>
{
    let mut tokens = vec![];

    while !source.is_empty() {
        let (rest, token) = lexer.next(source)?;
        // println!("{} {} {:?}", source.len(), source, token);
        source = rest;
        tokens.push(token);
    }
    Ok(tokens)
}

pub fn print_tokens<'a, T: Token<'a>>(tokens: Vec<T>) {
    println!("Tokens:");
    for (i, t) in tokens.iter().enumerate() {
        println!("#{:02}: {:?}", i + 1, t);
    }
}


fn main() {}
