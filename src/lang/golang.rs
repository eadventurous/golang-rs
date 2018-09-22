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
    // comment
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
        .add(r"//.*$", |c| Comment(c.get(0).unwrap().as_str()))
        .add(r"/\*.*?\*/", |c| Comment(c.get(0).unwrap().as_str()))

        .add(r"break", constant(Keyword(GoKeyword::Break)))
        .add(r"case", constant(Keyword(GoKeyword::Case)))
        .add(r"defer", constant(Keyword(GoKeyword::Chan)))
        .add(r"else", constant(Keyword(GoKeyword::Const)))
        .add(r"continue", constant(Keyword(GoKeyword::Continue)))

        .add(r"default", constant(Keyword(GoKeyword::Default)))
        .add(r"defer", constant(Keyword(GoKeyword::Defer)))
        .add(r"else", constant(Keyword(GoKeyword::Else)))
        .add(r"fallthroug", constant(Keyword(GoKeyword::Fallthrough)))
        .add(r"for", constant(Keyword(GoKeyword::For)))

        .add(r"func", constant(Keyword(GoKeyword::Func)))
        .add(r"go", constant(Keyword(GoKeyword::Go)))
        .add(r"goto", constant(Keyword(GoKeyword::Goto)))
        .add(r"if", constant(Keyword(GoKeyword::If)))
        .add(r"import", constant(Keyword(GoKeyword::Import)))

        .add(r"interface", constant(Keyword(GoKeyword::Interface)))
        .add(r"map", constant(Keyword(GoKeyword::Map)))
        .add(r"package", constant(Keyword(GoKeyword::Package)))
        .add(r"range", constant(Keyword(GoKeyword::Range)))
        .add(r"return", constant(Keyword(GoKeyword::Return)))

        .add(r"select", constant(Keyword(GoKeyword::Select)))
        .add(r"struct", constant(Keyword(GoKeyword::Struct)))
        .add(r"switch", constant(Keyword(GoKeyword::Switch)))
        .add(r"type", constant(Keyword(GoKeyword::Type)))
        .add(r"var", constant(Keyword(GoKeyword::Var)))

        .add(r"[[:digit:]]*\.[[:digit:]]*((e|E)(\+|-)?[[:digit:]]*)?i", |c| Literal(GoLiteral::Imaginary(c.get(0).unwrap().as_str())))
        .add(r"[[:digit:]]*(e|E)(\+|-)?[[:digit:]]*i", |c| Literal(GoLiteral::Imaginary(c.get(0).unwrap().as_str())))
        .add(r"\.[[:digit:]]*((e|E)(\+|-)?[[:digit:]]*)?i", |c| Literal(GoLiteral::Imaginary(c.get(0).unwrap().as_str())))
        .add(r"[[:digit:]]*i", |c| Literal(GoLiteral::Imaginary(c.get(0).unwrap().as_str())))

        .add(r"[[:digit:]]*\.[[:digit:]]*((e|E)(\+|-)?[[:digit:]]*)?", |c| Literal(GoLiteral::Float(c.get(0).unwrap().as_str())))
        .add(r"[[:digit:]]*(e|E)(\+|-)?[[:digit:]]*", |c| Literal(GoLiteral::Float(c.get(0).unwrap().as_str())))
        .add(r"\.[[:digit:]]*((e|E)(\+|-)?[[:digit:]]*)?", |c| Literal(GoLiteral::Float(c.get(0).unwrap().as_str())))

        .add(r"[1-9]+[[:digit:]]*", |c| Literal(GoLiteral::Integer(c.get(0).unwrap().as_str())))
        .add(r"0[0-7]*", |c| Literal(GoLiteral::Integer(c.get(0).unwrap().as_str())))
        .add(r"0(x|X)[[:xdigit:]]+", |c| Literal(GoLiteral::Integer(c.get(0).unwrap().as_str())))

        .add(r"\+=", constant(Operator(GoOperator::AddAssign)))
        .add(r"-=", constant(Operator(GoOperator::SubAssign)))
        .add(r"\*=", constant(Operator(GoOperator::MulAssign)))
        .add(r"/=", constant(Operator(GoOperator::QuoAssign)))
        .add(r"%=", constant(Operator(GoOperator::RemAssign)))

        .add(r"&=", constant(Operator(GoOperator::AndAssign)))
        .add(r"\|=", constant(Operator(GoOperator::OrAssign)))
        .add(r"\^=", constant(Operator(GoOperator::XorAssign)))
        .add(r"<<=", constant(Operator(GoOperator::ShlAssign)))
        .add(r">>=", constant(Operator(GoOperator::ShrAssign)))
        .add(r"&\^=", constant(Operator(GoOperator::AndNotAssign)))

        .add(r"&&", constant(Operator(GoOperator::LAnd)))
        .add(r"\|\|", constant(Operator(GoOperator::LOr)))
        .add(r"<-", constant(Operator(GoOperator::Arrow)))
        .add(r"\+\+", constant(Operator(GoOperator::Inc)))
        .add(r"--", constant(Operator(GoOperator::Dec)))

        .add(r"!=", constant(Operator(GoOperator::NEq)))
        .add(r"<=", constant(Operator(GoOperator::LEq)))
        .add(r">=", constant(Operator(GoOperator::GEq)))
        .add(r":=", constant(Operator(GoOperator::Define)))
        .add(r"\.\.\.", constant(Operator(GoOperator::Ellipsis)))

        .add(r"\(", constant(Operator(GoOperator::LParen)))
        .add(r"\[", constant(Operator(GoOperator::LBrack)))
        .add(r"\{", constant(Operator(GoOperator::LBrace)))
        .add(r",", constant(Operator(GoOperator::Comma)))
        .add(r"\.", constant(Operator(GoOperator::Period)))

        .add(r"\)", constant(Operator(GoOperator::RParen)))
        .add(r"\]", constant(Operator(GoOperator::RBrack)))
        .add(r"\}", constant(Operator(GoOperator::RBrace)))
        .add(r";", constant(Operator(GoOperator::Semicolon)))
        .add(r":", constant(Operator(GoOperator::Colon)))

        .add(r"==", constant(Operator(GoOperator::Eql)))
        .add(r"<", constant(Operator(GoOperator::Lss)))
        .add(r">", constant(Operator(GoOperator::Gtr)))
        .add(r"=", constant(Operator(GoOperator::Assign)))
        .add(r"!", constant(Operator(GoOperator::Not)))

        .add(r"&\^", constant(Operator(GoOperator::AndNot)))
        .add(r"&", constant(Operator(GoOperator::And)))
        .add(r"\|", constant(Operator(GoOperator::Or)))
        .add(r"\^", constant(Operator(GoOperator::Xor)))
        .add(r"<<", constant(Operator(GoOperator::Shl)))
        .add(r">>", constant(Operator(GoOperator::Shr)))

        .add(r"\+", constant(Operator(GoOperator::Add)))
        .add(r"-", constant(Operator(GoOperator::Sub)))
        .add(r"\*", constant(Operator(GoOperator::Mul)))
        .add(r"/", constant(Operator(GoOperator::Quo)))
        .add(r"%", constant(Operator(GoOperator::Rem)))

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

#[cfg(test)]
mod test {
    use super::*;
    use ::engine;

    #[test]
    fn golang() {
        let source = &r"2.71828";

        let tokens = engine(&make_lexer(), source).unwrap();
        assert_eq!(tokens, vec![Literal(GoLiteral::Float("2.71828"))]);
    }
}