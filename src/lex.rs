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
use std::cmp::Ordering;
use std::marker::PhantomData;
use std::rc::Rc;


pub struct Lexer<'a, T> {
    pairs: Rc<Vec<(Regex, Box<TokenFactory<'a, T>>)>>,
    skip_whitespaces: fn(&'a str) -> &'a str,
}

impl<'a, T> Clone for Lexer<'a, T> {
    fn clone(&self) -> Self {
        Lexer {
            pairs: Rc::clone(&self.pairs),
            skip_whitespaces: self.skip_whitespaces,
        }
    }
}


impl<'a, T> Lexer<'a, T>
    where T: Token<'a>
{
    /// Wrap lexer into `Tokens` stream without transfer of ownership.
    pub fn tokens(&self, source: &'a str) -> Tokens<'a, T> {
        Tokens::new(self.clone(), source)
    }

    /// Wrap lexer into `Tokens` stream with transfer of ownership.
    pub fn into_tokens(self, source: &'a str) -> Tokens<'a, T> {
        Tokens::new(self, source)
    }

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

/// Iterator over token stream, based on types `Lexer` and `Token`.
///
/// Engine which uses lexer to split source code into lexemes.
///
/// This engine is just an example of how processing whole file might be
/// implemented. While it is powerful enough to handle any source file,
/// it has some limitations: for example, it does not provide information
/// about location and span of generated tokens.
pub struct Tokens<'a, T> {
    lexer: Lexer<'a, T>,
    source: &'a str,
    error: bool,
}

impl<'a, T: Token<'a>> Tokens<'a, T> {
    fn new(lexer: Lexer<'a, T>, source: &'a str) -> Self {
        Tokens {
            lexer,
            source,
            error: false,
        }
    }
}


impl<'a, T> Iterator for Tokens<'a, T>
    where T: Token<'a> {
    type Item = Result<T, &'a str>;

    fn next(&mut self) -> Option<Result<T, &'a str>> {
        match self.error {
            false => match self.lexer.next(self.source) {
                Some(Ok((rest, token))) => {
                    self.source = rest;
                    Some(Ok(token))
                }
                Some(Err(_)) => {
                    self.error = false;
                    Some(Err(self.source))
                }
                None => None
            }
            true => None
        }
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
        Lexer { pairs: Rc::new(self.pairs), skip_whitespaces: self.skip_whitespaces }
    }
}


pub trait Token<'a>: Ord + Debug + Sized {
    fn describe(&self) -> String {
        format!("{:?}", self)
    }
}


pub trait TokenFactory<'a, T>
    where T: Token<'a>
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


pub trait Metrics {}

pub struct Bytes;

impl Metrics for Bytes {}

pub struct Chars;

impl Metrics for Chars {}


#[derive(Copy, Clone, Debug, Default)]
pub struct Location<M> {
    /// Line in source file, starting from 1.
    /// Such that `source.lines().nth(loc.line - 1)` is the referenced line.
    pub line: usize,
    /// Column at line `line` in source file, starting from 1.
    /// Such that `line.chars().nth(loc.column - 1)` is the referenced character.
    pub column: usize,
    /// Absolute position of character in source file starting from 0.
    /// Such that `source.chars().nth(loc.absolute)` is the references character.
    pub absolute: usize,
    _marker: PhantomData<M>,
}

impl<M: Metrics> Location<M> {
    pub fn new(line: usize, column: usize, absolute: usize) -> Self {
        Self { line, column, absolute, _marker: PhantomData }
    }

    /// Location of character addressed by absolute position in source `string`.
    ///
    /// # Panics
    ///
    /// `Err` if
    pub fn from(string: &str, absolute: usize) -> Self {
        if absolute > string.chars().count() {
            panic!("absolute position > length of string");
        }

        let mut line = 1;
        let mut column = 1;

        fn is_newline(c: char) -> bool {
            let c = c as u8;
            return c == 0x0d  // carriage returns (U+000D)
                || c == 0x0a; // newlines (U+000A)
        }

        for c in string.chars().take(absolute) {
            if is_newline(c) {
                line += 1;
                column = 1;
            } else {
                column += 1;
            }
        }

        Self { line, column, absolute, _marker: PhantomData }
    }
}

impl<M> PartialEq for Location<M> {
    fn eq(&self, other: &Location<M>) -> bool {
        self.absolute == other.absolute
    }
}

impl<M> Eq for Location<M> {}

impl<M> PartialOrd for Location<M> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<M> Ord for Location<M> {
    fn cmp(&self, other: &Location<M>) -> Ordering {
        self.absolute.cmp(&other.absolute)
    }
}


/// Span of substring in string.
///
/// # Invariant
///
/// - `end` location must be no less than `start` location.
/// - If end location is equal to start location, then span length is 1.
#[derive(Copy, Clone, Eq, PartialEq, Debug, Default)]
pub struct Span<M> {
    pub start: Location<M>,
    pub end: Location<M>,
}

impl<M> Span<M> {
    /// Span length, inclusive.
    ///
    /// # Panics
    ///
    /// Method will panic if span invariant does not hold.
    pub fn len(&self) -> usize {
        assert!(self.start.absolute <= self.end.absolute);
        1 + self.end.absolute - self.start.absolute
    }
}

impl Span<Chars> {
    pub fn slice(&self, string: &str) -> String {
        assert!(self.end.absolute < string.chars().count());
        string.chars()
              .skip(self.start.absolute)
              .take(self.len())
              .collect()
    }
}

impl Span<Bytes> {
    pub fn slice<'a>(&self, string: &'a str) -> &'a str {
        &string[self.start.absolute..=self.end.absolute]
    }
}


pub struct TokenMeta<T, M> {
    span: Span<M>,
    token: T,
}

#[derive(Debug)]
pub struct Error<'a, M> {
    span: Span<M>,
    rest: &'a str,
    description: Option<String>,
}


#[cfg(test)]
mod test {
    use super::*;

    const SOURCE: &str = "line one\nline two";

    #[test]
    fn test_span_char() {
        // span over "one\nline" substring
        let one_line_char: Span<Chars> = Span {
            start: Location::new(1, 6, 5),
            end: Location::new(2, 4, 12),
        };
        assert_eq!(one_line_char.slice(SOURCE), "one\nline");
        assert_eq!(one_line_char.len(), 8);

    }

    #[test]
    fn test_span_bytes() {
        let one_line_bytes: Span<Bytes> = Span {
            start: Location::new(1, 6, 5),
            end: Location::new(2, 4, 12),
        };
        assert_eq!(one_line_bytes.slice(SOURCE), "one\nline");
        assert_eq!(one_line_bytes.len(), 8);
    }
}