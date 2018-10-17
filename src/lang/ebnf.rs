//! # EBNF lexer
//!
//! EBNF (or Extended Backus-Naur Form) language consists of the following lexemes:
//! - terminals (e.g.: `"fn"`, `">="`);
//! - non-terminals (e.g.: `<Condition>`, `<Rule>`);
//! - 2 operators, namely: 'definition' (`::=`) and 'alternative' (`|`);
//! - repetitions (`{`, `}`);
//! - options (`[`, `]`);
//! - grouping parenthesis (`(`, `)`).
pub use self::{EbnfOperator::*, EbnfToken::*, Side::*};
use lex::{Lexer, LexerBuilder, Token};

#[derive(Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Debug)]
pub enum EbnfToken<'a> {
    Terminal(&'a str),
    NonTerminal(&'a str),
    Operator(EbnfOperator),
    Repeat(Side),
    Option(Side),
    Group(Side),
}

#[derive(Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Debug)]
pub enum EbnfOperator {
    /// Definition `"::="`
    Def,
    /// Alternative `"|"`
    Alt,
}

#[derive(Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Debug)]
pub enum Side {
    Start,
    End,
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

pub fn make_lexer<'a>() -> Lexer<'a, EbnfToken<'a>> {
    LexerBuilder::new()
        .skip_whitespaces(whitespace_filter)
        .add(r"::=", constant!(Operator(Def)))
        .add(r"\|", constant!(Operator(Alt)))
        .add(r"<(.+?)>", |c| NonTerminal(c.get(1).unwrap().as_str()))
        .add("\"(.*?)\"", |c| Terminal(c.get(1).unwrap().as_str()))
        .add(r"\{", constant!(Repeat(Start)))
        .add(r"\}", constant!(Repeat(End)))
        .add(r"\[", constant!(Option(Start)))
        .add(r"\]", constant!(Option(End)))
        .add(r"\(", constant!(Group(Start)))
        .add(r"\)", constant!(Group(End)))
        .build()
}

impl<'a> Token<'a> for EbnfToken<'a> {
    fn descriptor(&self) -> &'static str {
        match *self {
            Terminal(..) => "Terminal",
            NonTerminal(..) => "NonTerminal",
            Operator(Def) => "::=",
            Operator(Alt) => "|",
            Repeat(Start) => "{",
            Repeat(End) => "}",
            Option(Start) => "[",
            Option(End) => "]",
            Group(Start) => "(",
            Group(End) => ")",
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use lex::TokensExt;

    const SOURCE: &str = r#"
        <A> ::= (<B> | {"c"}) [<D>]
    "#;

    const TOKENS: &[EbnfToken] = &[
        NonTerminal("A"),
        Operator(Def),
        Group(Start),
        NonTerminal("B"),
        Operator(Alt),
        Repeat(Start),
        Terminal("c"),
        Repeat(End),
        Group(End),
        Option(Start),
        NonTerminal("D"),
        Option(End),
    ];

    #[test]
    fn test_lexer() {
        let tokens: Vec<_> = make_lexer().into_tokens(SOURCE).into_raw().collect();

        assert_eq!(tokens, TOKENS);
    }
}