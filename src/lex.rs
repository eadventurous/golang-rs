//! Lexer presented here is generic about language and
//! based on regular expressions.
//!
//! `LexerBuilder` type uses [Builder pattern] to create `Lexer` instances.
//!
//! `Token` is generic trait that supposed to be implemented by `enum` of
//! particular language's all possible tokens.
//!
//! `TokenFactory` is just a fancy way to say "convert regex capture to a
//! token".
//!
//! [Builder pattern]: https://en.wikipedia.org/wiki/Builder_pattern
use regex::{Captures, Regex};
use std::fmt::Debug;


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


pub trait Token<'a>: Ord + Debug + Sized {
    fn describe(&self) -> String {
        format!("{:?}", self)
    }
}


pub trait TokenFactory<'a, T> where T: Token<'a>
{
    fn token(&self, c: Captures<'a>) -> T;
}

/// ```rust
/// let factory_comma = |_| Tok::Comma;
/// let factory_ident = |c| Tok::Ident(c.as_str());
/// ```
impl<'a, T, F> TokenFactory<'a, T> for F
    where
        T: Token<'a>,
        F: Fn(Captures<'a>) -> T {
    fn token(&self, c: Captures<'a>) -> T {
        self(c)
    }
}
