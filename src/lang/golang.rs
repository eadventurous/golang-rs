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
    /// From golang specs:
    ///
    /// A rune literal represents a rune constant, an integer value identifying a Unicode code point.
    ///
    /// ```
    /// rune_lit         = "'" ( unicode_value | byte_value ) "'" .
    /// unicode_value    = unicode_char | little_u_value | big_u_value | escaped_char .
    /// byte_value       = octal_byte_value | hex_byte_value .
    /// octal_byte_value = `\` octal_digit octal_digit octal_digit .
    /// hex_byte_value   = `\` "x" hex_digit hex_digit .
    /// little_u_value   = `\` "u" hex_digit hex_digit hex_digit hex_digit .
    /// big_u_value      = `\` "U" hex_digit hex_digit hex_digit hex_digit
    ///                            hex_digit hex_digit hex_digit hex_digit .
    /// escaped_char     = `\` ( "a" | "b" | "f" | "n" | "r" | "t" | "v" | `\` | "'" | `"` ) .
    /// ```
    Rune(&'a str),
}

pub fn make_lexer<'a>() -> Lexer<'a, GoToken<'a>> {
    let constant = |x| { move |_| x };

    let rune = r#"(?x)
        ' # open quote
        ( # unicode_value = unicode_char | little_u_value | big_u_value | escaped_char

              # unicode_char = /* an arbitrary Unicode code point except newline */
                [^\\\n]
            | # little_u_value
                \\u ([0-9A-Fa-f]){4}  # TODO: change to [[:xdigit:]]
            | # big_u_value
                \\U ([0-9A-Fa-f]){8}  # TODO: change to [[:xdigit:]]
            | # escaped_char
                \\   [abfnrtv\\'"]

        | # byte value = octal_byte_value | hex_byte_value

              # octal_byte_value
                \\   [0-7]{3}
            | # hex_byte_value
                \\x ([0-9A-Fa-f]){2}  # TODO: change to [[:xdigit:]]
        )
        ' # close quote
    "#;


    LexerBuilder::new()
        .add(r"-", constant(Operator(GoOperator::Dec)))
        .add(rune, |c| GoToken::Literal(GoLiteral::Rune(c.get(1).unwrap().as_str())))
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

    #[test]
    fn test_rune() {
        let lexer = make_lexer();

        let valid_runes = [
            r"'a'",
            r"'ä'",
            r"'本'",
            r"'\t'",
            r"'\000'",
            r"'\007'",
            r"'\377'",
            r"'\x07'",
            r"'\xff'",
            r"'\u12e4'",
            r"'\U00101234'",
            r"'\''",         // rune literal containing single quote character
        ];
        let illegal_runes = [
            r"'aa'",         // illegal: too many characters
            r"'\xa'",        // illegal: too few hexadecimal digits
            r"'\0'",         // illegal: too few octal digits
            // Regexp-based lexer cannot detect surrogate half,
            // r"'\uDFFF'",     // illegal: surrogate half
            // ...nor it is capable of understanding Unicode code points.
            // r"'\U00110000'", // illegal: invalid Unicode code point
        ];
        for rune in valid_runes.into_iter() {
            assert_eq!(lexer.next(rune).unwrap().1,
                       GoToken::Literal(GoLiteral::Rune(&rune[1..rune.len() - 1])));
        }
        for rune in illegal_runes.into_iter() {
            assert!(lexer.next(rune).is_err());
        }
    }
}