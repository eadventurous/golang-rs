//! # BNF lexer
//!
//! BNF language consists of the following lexemes:
//! - terminals (e.g.: `"fn"`, `">="`),
//! - non-terminals (e.g.: `<Condition>`, `<Rule>`)
//! - 2 operators, namely: 'definition' (`::=`) and 'alternative' (`|`).
use lex::{Lexer, LexerBuilder, Token};

#[derive(Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Debug)]
pub enum BnfToken<'a> {
    Terminal(&'a str),
    NonTerminal(&'a str),
    Operator(BnfOperator),
}

#[derive(Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Debug)]
pub enum BnfOperator {
    /// "::="
    Equals,
    /// Alternative "|"
    Alt,
}

fn is_whitespace(c: char) -> bool {
    let c = c as u8;
    return c == 0x20 // spaces (U+0020)
        || c == 0x09 // horizontal tabs (U+0009)
        || c == 0x0d // carriage returns (U+000D)
        || c == 0x0a; // newlines (U+000A)
}

fn whitespace_filter(source: &str) -> &str {
    for (i, c) in source.char_indices() {
        if !is_whitespace(c) {
            return &source[i..];
        }
    }
    &source[source.len()..]
}

pub fn make_lexer<'a>() -> Lexer<'a, BnfToken<'a>> {
    let constant = |x| move |_| x;
    LexerBuilder::new()
        .skip_whitespaces(whitespace_filter)
        .add(r"::=", constant(BnfToken::Operator(BnfOperator::Equals)))
        .add(r"\|", constant(BnfToken::Operator(BnfOperator::Alt)))
        .add(r"<(.+?)>", |c| {
            BnfToken::NonTerminal(c.get(1).unwrap().as_str())
        }).add("\"(.*?)\"", |c| {
            BnfToken::Terminal(c.get(1).unwrap().as_str())
        }).build()
}

impl<'a> Token<'a> for BnfToken<'a> {
    fn descriptor(&self) -> &'static str {
        match *self {
            BnfToken::Terminal(..) => "Terminal",
            BnfToken::NonTerminal(..) => "NonTerminal",
            BnfToken::Operator(BnfOperator::Equals) => "::=",
            BnfToken::Operator(BnfOperator::Alt) => "|",
        }
    }
}
