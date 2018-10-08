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
use std::fmt::{self, Debug, Formatter};
use std::cmp::Ordering;
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
    location: Location<Bytes>,
}

impl<'a, T: Token<'a>> Tokens<'a, T> {
    fn new(lexer: Lexer<'a, T>, source: &'a str) -> Self {
        Tokens {
            lexer,
            source,
            error: false,
            location: Default::default(),
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


pub trait Metrics: Copy + Clone + Debug + Default + Ord + PartialOrd + Eq + PartialEq {
    fn len(string: &str) -> usize;
    fn get(location: &Location<Self>, string: &str) -> Option<char>;
    fn slice<'a>(span: &Span<Self>, string: &'a str) -> &'a str;
    fn location_add(location: Location<Self>, s: &str) -> Location<Self>;
    fn location(string: &str, absolute: usize) -> Location<Self> {
        if absolute >= Self::len(string) {
            panic!("absolute position >= length of string");
        }

        assert!(Self::len(string) > 0);

        // Breaking the invariant of column >= 1, but it's OK because string is non-empty.
        // Also `absolute` should be -1 for this case, but it is usize, so instead we will fix it later.
        let mut location = Location { line: 1, column: 0, absolute: 0, was_newline: false, metrics: Default::default() };
        location += &string[..absolute + 1];
        location.absolute -= 1;
        location
    }
}

#[derive(Copy, Clone, Debug, Default, Ord, PartialOrd, Eq, PartialEq)]
pub struct Bytes;

impl Bytes {
    fn is_newline(c: u8) -> bool {
        return c == 0x0d  // carriage returns (U+000D)
            || c == 0x0a; // newlines (U+000A)
    }
}

impl Metrics for Bytes {
    fn len(string: &str) -> usize {
        string.len()
    }

    fn get(location: &Location<Self>, string: &str) -> Option<char> {
        if location.absolute >= string.len() {
            None
        } else {
            Some(string.as_bytes()[location.absolute] as char)
        }
    }

    fn slice<'a>(span: &Span<Self>, string: &'a str) -> &'a str {
        &string[span.start.absolute..=span.end.absolute]
    }

    fn location_add(mut location: Location<Self>, s: &str) -> Location<Self> {
        // newline character counts as a part of its preceding line.
        for c in s.bytes() {
            if location.was_newline {
                location.line += 1;
                location.column = 1;
            } else {
                location.column += 1;
            }
            location.was_newline = Self::is_newline(c);
        }
        location.absolute += s.bytes().count();
        location
    }
}

#[derive(Copy, Clone, Debug, Default, Ord, PartialOrd, Eq, PartialEq)]
pub struct Chars;

impl Chars {
    fn is_newline(c: char) -> bool {
        let c = c as u8;
        return c == 0x0d  // carriage returns (U+000D)
            || c == 0x0a; // newlines (U+000A)
    }
}

impl Metrics for Chars {
    fn len(string: &str) -> usize {
        string.chars().count()
    }

    fn get(location: &Location<Self>, string: &str) -> Option<char> {
        string.chars().nth(location.absolute)
    }

    fn slice<'a>(span: &Span<Self>, string: &'a str) -> &'a str {
        assert!(span.end.absolute < Chars::len(string));

        let skip: usize = string.chars().take(span.start.absolute).map(char::len_utf8).sum();
        let take: usize = (&string[skip..]).chars().take(span.len()).map(char::len_utf8).sum();

        &string[skip..skip + take]
    }

    fn location_add(mut location: Location<Self>, s: &str) -> Location<Self> {
        for c in s.chars() {
            if location.was_newline {
                location.line += 1;
                location.column = 1;
            } else {
                location.column += 1;
            }
            location.absolute += 1;
            location.was_newline = Chars::is_newline(c);
        }
        location
    }
}


#[derive(Copy, Clone, Debug)]
pub struct Location<M: Metrics> {
    /// Line in source file, starting from 1.
    /// Such that `source.lines().nth(loc.line - 1)` is the referenced line.
    pub line: usize,
    /// Column at line `line` in source file, starting from 1.
    /// Such that `line.chars().nth(loc.column - 1)` is the referenced byte/character.
    pub column: usize,
    /// Absolute position of byte/character in source file starting from 0.
    /// Such that `source.chars().nth(loc.absolute)` is the references byte/character.
    pub absolute: usize,
    /// Was the last character a newline?
    pub was_newline: bool,
    /// Metrics marker
    pub metrics: M,
//    _marker: PhantomData<M>,
}

impl<M: Metrics> Location<M> {
    /// Compose new `Location` from parts.
    ///
    /// # Panics
    ///
    /// If at least one of `line` or `column` arguments is zero, method will panic.
    ///
    pub fn new(line: usize, column: usize, absolute: usize) -> Self {
        assert!(line >= 1);
        assert!(column >= 1);

        Self { line, column, absolute, ..Default::default() }
    }

    /// Location of character addressed by absolute position in source `string`.
    ///
    /// # Panics
    ///
    /// If absolute position is greater or equal to length of string (according to `Metrics`).
    pub fn from(string: &str, absolute: usize) -> Self {
        M::location(string, absolute)
    }

    pub fn get(&self, source: &str) -> Option<char> {
        M::get(self, source)
    }
}

impl<M: Metrics> Default for Location<M> {
    fn default() -> Self {
        Self {
            line: 1,
            column: 1,
            absolute: 0,
            was_newline: false,
            metrics: Default::default(),
        }
    }
}

impl<M: Metrics> PartialEq for Location<M> {
    fn eq(&self, other: &Location<M>) -> bool {
        self.absolute == other.absolute
    }
}

impl<M: Metrics> Eq for Location<M> {}

impl<M: Metrics> PartialOrd for Location<M> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<M: Metrics> Ord for Location<M> {
    fn cmp(&self, other: &Location<M>) -> Ordering {
        self.absolute.cmp(&other.absolute)
    }
}

impl<M: Metrics, S: AsRef<str>> ::std::ops::Add<S> for Location<M> {
    type Output = Location<M>;

    fn add(self, rhs: S) -> <Self as ::std::ops::Add<S>>::Output {
        M::location_add(self, rhs.as_ref())
    }
}

impl<M: Metrics, S: AsRef<str>> ::std::ops::AddAssign<S> for Location<M> {
    fn add_assign(&mut self, rhs: S) {
        *self = M::location_add(*self, rhs.as_ref());
    }
}


/// Span of substring in string.
///
/// # Invariant
///
/// - `end` location must be no less than `start` location.
/// - If end location is equal to start location, then span length is 1.
#[derive(Copy, Clone, Eq, PartialEq, Debug, Default)]
pub struct Span<M: Metrics> {
    pub start: Location<M>,
    pub end: Location<M>,
}

impl<M: Metrics> Span<M> {
    /// Make span from absolute positions (with both ends inclusive).
    pub fn from(string: &str, start: usize, end: usize) -> Self {
        Self {
            start: Location::from(string, start),
            end: Location::from(string, end),
        }
    }

    /// Span length, inclusive.
    ///
    /// # Panics
    ///
    /// Method will panic if span invariant does not hold.
    pub fn len(&self) -> usize {
        assert!(self.start.absolute <= self.end.absolute);
        1 + self.end.absolute - self.start.absolute
    }

    /// Slice substring out of source `string`, metrics-specific.
    pub fn slice<'a>(&self, string: &'a str) -> &'a str {
        M::slice(self, string)
    }

    /// # Returns
    ///
    /// Pairs of top-to-bottom lines spanned by self with spans for them, one per line.
    ///
    /// - First item spans from `self.start.column` location up to the end of line.
    /// - Every intermediate line spans from 1st column up to (but excluding) line terminator.
    /// - Last line spans from 1st column up to `self.end.column` location.
    pub fn lines<'a>(&self, source: &'a str) -> LinesWithSpans<'a, M> {
        if self.is_multiline() {
            let first = self.start.line;
            let last = self.end.line;
            let total = 1 + last - first;
            assert!(last > first);
            let intermediates = total - 2;

            let mut vec = vec![];
            let mut lines = source.lines().skip(first - 1).take(total);

            // first
            let line = lines.next().unwrap();
            let span = Span::<M> {
                start: Location::from(line, self.start.column - 1),
                end: Location::from(line, M::len(line) - 1),
            };
            vec.push((line, span));

            // intermediates
            for _ in 0..intermediates {
                let line = lines.next().unwrap();
                let span = Span::<M> {
                    start: Location::from(line, 0),
                    end: Location::from(line, M::len(line) - 1),
                };
                vec.push((line, span))
            }

            // last
            let line = lines.next().unwrap();
            let span = Span::<M> {
                start: Location::from(line, 0),
                end: Location::from(line, self.end.column - 1),
            };
            vec.push((line, span));

            vec
        } else {
            let line = source.lines().nth(self.start.line - 1).unwrap();
            let span = Span::<M> {
                start: Location::new(1, self.start.column, self.start.column - 1),
                end: Location::new(1, self.end.column, self.end.column - 1),
            };
            vec![(line, span)]
        }
    }

    /// Returns true if `self` has both ends on the same line.
    fn is_multiline(&self) -> bool {
        self.start_line() != self.end_line()
    }

    /// Shortcut to `self.start.line`.
    pub fn start_line(&self) -> usize { self.start.line }

    /// Shortcut to `self.end.line`.
    pub fn end_line(&self) -> usize { self.end.line }

    /// Count of intermediate lines spanned by `self`.
    pub fn intermediate_lines(&self) -> usize {
        if self.is_multiline() { self.end.line - self.start.line - 1 } else { 0 }
    }

    /// Count of total lines spanned by `self`.
    pub fn total_lines(&self) -> usize {
        if self.is_multiline() { self.end.line - self.start.line + 1 } else { 1 }
    }
}

pub type LinesWithSpans<'a, M> = Vec<(&'a str, Span<M>)>;

pub struct TokenMeta<T> {
    pub span: Span<Bytes>,
    pub token: T,
}

impl<T> Clone for TokenMeta<T> where T: Clone {
    fn clone(&self) -> Self {
        Self { span: self.span, token: self.token.clone() }
    }
}

impl<T> Debug for TokenMeta<T> where T: Debug {
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
        write!(f, "TokenMeta {{ span: {:?}, token: {:?} }}", self.span, self.token)
    }
}

#[derive(Debug)]
pub struct Error<'a, M> where M: Metrics {
    pub filename: &'a str,
    pub span: Span<M>,
    pub source: &'a str,
    pub rest: &'a str,
    pub description: Option<String>,
}

impl<'a, M> fmt::Display for Error<'a, M> where M: Metrics {
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
        writeln!(f, "Error at {}:{}:{}",
                 self.filename,
                 self.span.start.line,
                 self.span.start.column,
        )?;
        for (line, (string, span)) in self.span.lines(self.source).into_iter().enumerate() {
            let line = line + self.span.start.line;
            let before = if span.start.absolute == 0 { 0 } else {
                Span::<M>::from(string, 0, span.start.absolute - 1)
                    .slice(string)
                    .chars()
                    .count()
            };
            let slice = span.slice(string);
            let len = slice.chars().count();

            writeln!(f, "{: <4}| {}", line, string)?;
            writeln!(f, "    | {}{}", " ".repeat(before), "^".repeat(len))?;
        }
        if let Some(ref description) = self.description {
            writeln!(f, "{}", description)?;
        }
        Ok(())
    }
}


#[cfg(test)]
mod test {
    use super::*;

    const SOURCE: &str = "line one\nline two";
    const ONE_LINE_BYTES_SPAN: Span<Bytes> = Span {
        start: Location { line: 1, column: 6, absolute: 5, was_newline: false, metrics: Bytes },
        end: Location { line: 2, column: 4, absolute: 12, was_newline: false, metrics: Bytes },
    };

    #[test]
    fn test_location_new() {
        // 'o'
        let loc = Location::<Bytes>::new(1, 6, 5);
        assert_eq!(1, loc.line);
        assert_eq!(6, loc.column);
        assert_eq!(5, loc.absolute);

        // 'n'
        let loc = Location::<Bytes>::new(2, 3, 11);
        assert_eq!(2, loc.line);
        assert_eq!(3, loc.column);
        assert_eq!(11, loc.absolute);
    }

    #[test]
    fn test_location_from() {
        // 'o'
        let loc = Location::<Bytes>::from(SOURCE, 5);
        assert_eq!(1, loc.line);
        assert_eq!(6, loc.column);
        assert_eq!(5, loc.absolute);

        // 'n'
        let loc = Location::<Bytes>::from(SOURCE, 12);
        assert_eq!(2, loc.line);
        assert_eq!(4, loc.column);
        assert_eq!(12, loc.absolute);
    }

    #[test]
    fn test_location_add() {
        const S: &str = "hello\nworld";
        let mut loc = Location::<Bytes>::from(S, S.len() - 1);
        assert_eq!(2, loc.line);
        assert_eq!(5, loc.column);
        assert_eq!(10, loc.absolute);

        loc += "\n";
        assert_eq!(2, loc.line);
        assert_eq!(6, loc.column);
        assert_eq!(11, loc.absolute);

        loc += "abc";
        assert_eq!(3, loc.line);
        assert_eq!(3, loc.column);
        assert_eq!(14, loc.absolute);
    }

    #[test]
    fn test_span_from() {
        assert_eq!(ONE_LINE_BYTES_SPAN, Span::<Bytes>::from(SOURCE, 5, 12));
    }


    #[test]
    fn test_span_char() {
        // span over "one\nline" substring
        let one_line_char = Span::<Chars>::from(SOURCE, 5, 12);
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

    #[test]
    fn test_meta_token() {
        #[derive(Debug)]
        struct Tok;

        assert_eq!("Tok".to_owned(), format!("{:?}", Tok));

        let _meta = TokenMeta {
            span: Span {
                start: Location::new(1, 1, 0),
                end: Location::new(2, 1, 5),
            },
            token: Tok,
        };
    }

    const NUMBERS: &str = "\
            one\n\
            two word\n\
            tree\n\
            four\n\
            five to wolf\n\
            six";

    const NUMBERS_BYTES_SPAN: Span<Bytes> = Span {
        start: Location {
            line: 2,
            column: 5,
            absolute: 8,
            was_newline: false,
            metrics: Bytes,
        },
        end: Location {
            line: 5,
            column: 7,
            absolute: 29,
            was_newline: false,
            metrics: Bytes,
        },
    };

    #[test]
    fn test_span_lines() {
        let slice = NUMBERS_BYTES_SPAN.slice(NUMBERS);
        assert_eq!("word\ntree\nfour\nfive to", slice);

        let lines = NUMBERS_BYTES_SPAN.lines(NUMBERS);

        assert_eq!(lines.len(), 4);
        assert_eq!(lines[0].1, Span::from("two word", 4, 7));
        assert_eq!(lines[1].1, Span::from("tree", 0, 3));
        assert_eq!(lines[2].1, Span::from("four", 0, 3));
        assert_eq!(lines[3].1, Span::from("five to wolf", 0, 6));
    }

    #[test]
    fn test_error() {
        let error = Error {
            filename: "<stdin>",
            span: NUMBERS_BYTES_SPAN,
            source: NUMBERS,
            rest: "",
            description: Some("Custom error message.".to_owned()),
        };

        let expected = "\
Error at <stdin>:2:5
2   | two word
    |     ^^^^
3   | tree
    | ^^^^
4   | four
    | ^^^^
5   | five to wolf
    | ^^^^^^^
Custom error message.
";
        assert_eq!(expected.to_owned(), format!("{}", error));
    }
}
