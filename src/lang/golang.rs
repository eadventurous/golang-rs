use super::{Token, TokenFactory};
use ::{Lexer, LexerBuilder};
use regex::Match;
pub use self::GoToken::*;

#[derive(Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Debug)]
pub enum GoToken<'a> {
    /// identifiers
    Ident(&'a str),
    /// keywords
    Keyword(GoKeyword),
    /// operators and punctuation,
    Operator(GoOperator),
    // literals
    Literal(GoLiteral<'a>),
    // White space
    Comment(&'a str),
}

/// Go programming language keywords
#[derive(Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Debug)]
pub enum GoKeyword {
    Break,
    Default,
    Func,
    Interface,
    Select,
    Case,
    Defer,
    Go,
    Map,
    Struct,
    Chan,
    Else,
    Goto,
    Package,
    Switch,
    Const,
    Fallthrough,
    If,
    Range,
    Type,
    Continue,
    For,
    Import,
    Return,
    Var,
}

#[derive(Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Debug)]
pub enum GoOperator {
    Add,
    Sub,
    Mul,
    Quo,
    Rem,
    
    And,
    Or,
    Xor,
    Shl,
    Shr,
    AndNot,

    AddAssign,
    SubAssign,
    QuoAssign,
    RemAssign,
    MulAssign,

    AndAssign,
    OrAssign,
    XorAssign,
    ShlAssign,
    ShrAssign,
    AndNotAssign,

    LAnd,
    LOr,
    Arrow,
    Inc,
    Dec,

    Eql,
    Lss,
    Gtr,
    Assign,
    Not,

    NEq,
    LEq,
    GEq,
    Define,
    Ellipsis,

    LParen,
    LBrack,
    LBrace,
    Comma,
    Period,

    RParen,
    RBrack,
    RBrace,
    Semicolon,
    Colon,
}

#[derive(Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Debug)]
pub enum GoLiteral<'a> {
    String(&'a str),
    Integer(&'a str),
    Float(&'a str),
    Imaginary(&'a str),
    Rune(&'a str),
}

pub fn make_lexer<'a>() -> Lexer<'a, GoToken<'a>> {
    let constant = |x| { move |_| x };
    LexerBuilder::new()
        .add(r"-", constant(Operator(GoOperator::Dec)))
        .add(r"[^<>\[\],.+\-]+", |c| GoToken::Comment(c.get(0).unwrap().as_str()))
        .build() 
}


impl<'a> Token<'a> for GoToken<'a> {
    fn describe(&self) -> String {
        match *self {
            GoToken::Ident(ref id) => id.to_string(),
            GoToken::Keyword(ref kw) => format!("{:?}", kw),
            _ => format!("{:?}", self),
        }
    }
}