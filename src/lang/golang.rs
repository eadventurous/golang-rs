use lex::{Lexer, LexerBuilder, Token};

pub use self::GoToken::*;

#[derive(Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Debug)]
pub enum GoToken<'a> {
    /// identifiers
    Ident(&'a str),
    /// keywords
    Keyword(GoKeyword),
    /// operators and punctuation,
    Operator(GoOperator),
    /// Literal values like strings and numbers.
    Literal(GoLiteral<'a>),
    /// Single-line and multi-line comments
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
    /// ```raw_string_lit         = "`" { unicode_char | newline } "`" .```
    RawString(&'a str),
    /// ```interpreted_string_lit = `"` { unicode_value | byte_value } `"` .```
    InterpretedString(&'a str),
    Integer(&'a str),
    Float(&'a str),
    Imaginary(&'a str),
    /// From golang specs:
    ///
    /// A rune literal represents a rune constant, an integer value identifying a Unicode code point.
    ///
    /// ```ebnf
    /// rune_lit         = "'" ( unicode_value | byte_value ) "'" .
    /// unicode_value    = unicode_char | little_u_value | big_u_value | escaped_char .
    /// byte_value       = octal_byte_value | hex_byte_value .
    /// octal_byte_value = `\\` octal_digit octal_digit octal_digit .
    /// hex_byte_value   = `\\` "x" hex_digit hex_digit .
    /// little_u_value   = `\\` "u" hex_digit hex_digit hex_digit hex_digit .
    /// big_u_value      = `\\` "U" hex_digit hex_digit hex_digit hex_digit
    ///                            hex_digit hex_digit hex_digit hex_digit .
    /// escaped_char     = `\\` ( "a" | "b" | "f" | "n" | "r" | "t" | "v" | `\` | "'" | `"` ) .
    /// ```
    Rune(&'a str),
}

fn is_whitespace(c: char) -> bool {
    let c = c as u8;
    return c == 0x20 // spaces (U+0020)
        || c == 0x09 // horizontal tabs (U+0009)
        || c == 0x0d // carriage returns (U+000D)
        || c == 0x0a;// newlines (U+000A)
}

fn whitespace_filter(source: &str) -> &str {
    for (i, c) in source.char_indices() {
        if !is_whitespace(c) {
            return &source[i..];
        }
    }
    &source[source.len()..]
}

pub fn make_lexer<'a>() -> Lexer<'a, GoToken<'a>> {
    let constant = |x| { move |_| x };

    let rune = r#"(?x)
        ' # open quote
        ( # unicode_value = unicode_char | little_u_value | big_u_value | escaped_char

              # unicode_char = /* an arbitrary Unicode code point except newline */
              # Note: also except close quote and backslash [as it must be followed by other character(s)]
                [^\\\n']
            | # little_u_value
                \\u [[:xdigit:]]{4}
            | # big_u_value
                \\U [[:xdigit:]]{8}
            | # escaped_char
                \\   [abfnrtv\\'"]

        | # byte value = octal_byte_value | hex_byte_value

              # octal_byte_value
                \\   [0-7]{3}
            | # hex_byte_value
                \\x [[:xdigit:]]{2}
        )
        ' # close quote
    "#;

    // raw_string_lit         = "`" { unicode_char | newline } "`" .
    let raw_string = r#"(?x)
        ` # open quote
        ( # group 1
            (?: # unicode_char
                [^`]
            |   # newline
                \n
            )*?
        ) # end group 1
        ` # close quote
    "#;

    // interpreted_string_lit = `"` { unicode_value | byte_value } `"` .
    let interpreted_string = r#"(?x)
        " # open quote
        ( # group 1
            (?: # unicode_value = unicode_char | little_u_value | big_u_value | escaped_char

                  # unicode_char = /* an arbitrary Unicode code point except newline */
                  # Note: also except close quote and backslash [as it must be followed by other character(s)]
                    [^\\\n"]
                | # little_u_value
                    \\u [[:xdigit:]]{4}
                | # big_u_value
                    \\U [[:xdigit:]]{8}
                | # escaped_char
                    \\   [abfnrtv\\'"]

            |   # byte value = octal_byte_value | hex_byte_value

                  # octal_byte_value
                    \\   [0-7]{3}
                | # hex_byte_value
                    \\x [[:xdigit:]]{2}
            )*
        ) # end group 1
        " # close quote

    "#;

    LexerBuilder::new()
        .skip_whitespaces(whitespace_filter)
        .add(r"//([^\n]*)\n?", |c| Comment(c.get(1).unwrap().as_str()))
        .add(r"(?s)/\*(.*?)\*/", |c| Comment(c.get(1).unwrap().as_str()))

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

        .add(r"[[:digit:]]+\.[[:digit:]]*((e|E)(\+|-)?[[:digit:]]*)?i", |c| Literal(GoLiteral::Imaginary(c.get(0).unwrap().as_str())))
        .add(r"[[:digit:]]+(e|E)(\+|-)?[[:digit:]]*i", |c| Literal(GoLiteral::Imaginary(c.get(0).unwrap().as_str())))
        .add(r"\.[[:digit:]]+((e|E)(\+|-)?[[:digit:]]*)?i", |c| Literal(GoLiteral::Imaginary(c.get(0).unwrap().as_str())))
        .add(r"[[:digit:]]+i", |c| Literal(GoLiteral::Imaginary(c.get(0).unwrap().as_str())))

        .add(r"[[:digit:]]+\.[[:digit:]]*((e|E)(\+|-)?[[:digit:]]*)?", |c| Literal(GoLiteral::Float(c.get(0).unwrap().as_str())))
        .add(r"[[:digit:]]+(e|E)(\+|-)?[[:digit:]]*", |c| Literal(GoLiteral::Float(c.get(0).unwrap().as_str())))
        .add(r"\.[[:digit:]]+((e|E)(\+|-)?[[:digit:]]*)?", |c| Literal(GoLiteral::Float(c.get(0).unwrap().as_str())))

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

        .add(rune, |c| GoToken::Literal(GoLiteral::Rune(c.get(1).unwrap().as_str())))

        .add(raw_string, |c| GoToken::Literal(GoLiteral::RawString(c.get(1).unwrap().as_str())))
        .add(interpreted_string, |c| GoToken::Literal(GoLiteral::InterpretedString(c.get(1).unwrap().as_str())))

        .add(r"(\p{L}|_)(\p{L}|_|\p{Nd})*", |c| Ident(c.get(0).unwrap().as_str()))

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
    use ::{engine, token};

    #[test]
    fn test_id() {
        let lexer = make_lexer();

        let valid_id = [
            r"a",
            r"_x9",
            r"ThisVariableIsExported",
            r"αβ",
            r"__var__",
            r"e",
            r"i",
        ];
        let illegal_id = [
            r"6a",         // illegal: can't start with digit
            r".a",        // illegal: can't start with dot
        ];
        for id in valid_id.into_iter() {
            assert_eq!(token(lexer.next(id)),
                       GoToken::Ident(&id));
        }
        for id in illegal_id.into_iter() {
            match lexer.next(id) {
                Some(Ok((_, GoToken::Ident(_)))) => panic!(),
                _ => {}
            }
        }
    }

    #[test]
    fn test_imaginary() {
        let lexer = make_lexer();

        let valid_imaginary = [
            r"0i",
            r"011i",
            r"0.i",
            r"2.71828i",
            r"1.e+0i",
            r"6.67428e-11i",
            r"1E6i",
            r".25i",
            r".12345E+5i",
        ];
        let illegal_imaginary = [
            r"e6i",         // illegal: can't start with i
            r"..6i",        // illegal: too many dots
            r"82",         // illegal: it is integer
            r"4.5",        // illegal: it is float
            r"i",           //illegal: can't start with i
        ];
        for imaginary in valid_imaginary.into_iter() {
            assert_eq!(token(lexer.next(imaginary)),
                       GoToken::Literal(GoLiteral::Imaginary(&imaginary)));
        }
        for imaginary in illegal_imaginary.into_iter() {
            match lexer.next(imaginary) {
                Some(Ok((_, GoToken::Literal(GoLiteral::Imaginary(_))))) => panic!(),
                _ => {}
            }
        }
    }

    #[test]
    fn test_float() {
        let lexer = make_lexer();

        let valid_floats = [
            r"0.",
            r"72.40",
            r"072.40",
            r"2.71828",
            r"1.e+0",
            r"6.67428e-11",
            r"1E6",
            r".25",
            r".12345E+5",
        ];
        let illegal_floats = [
            r"e6",         // illegal: can't start with exponent
            r"..6",        // illegal: too many dots
            r"82",         // illegal: it is integer
        ];
        for float in valid_floats.into_iter() {
            assert_eq!(token(lexer.next(float)),
                       GoToken::Literal(GoLiteral::Float(&float)));
        }
        for float in illegal_floats.into_iter() {
            match lexer.next(float) {
                Some(Ok((_, Literal(GoLiteral::Float(_))))) => panic!(),
                _ => {}
            }
        }
    }

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
            assert_eq!(token(lexer.next(rune)),
                       GoToken::Literal(GoLiteral::Rune(&rune[1..rune.len() - 1])));
        }
        for rune in illegal_runes.into_iter() {
            assert!(lexer.next(rune).unwrap().is_err());
        }
    }

    #[test]
    fn test_string_lit() {
        let lexer = make_lexer();

        let raw_strings = [
            r"`abc`",                // same as "abc"
            r"`\n
\n`",                                // same as "\\n\n\\n"
        ];
        let interpreted_strings = [
            r#""\n""#,
            r#""\"""#,                   // same as `"`
            r#""Hello, world!\n""#,
            r#""日本語""#,
            r#""\u65e5本\U00008a9e""#,
            r#""\xff\u00FF""#,
        ];

        for s in raw_strings.into_iter() {
            assert_eq!(token(lexer.next(s)),
                       GoToken::Literal(GoLiteral::RawString(&s[1..s.len() - 1])));
        }

        for s in interpreted_strings.into_iter() {
            assert_eq!(token(lexer.next(s)),
                       GoToken::Literal(GoLiteral::InterpretedString(&s[1..s.len() - 1])));
        }
    }

    #[test]
    fn test_white_space() {
        let lexer = make_lexer();
        let source = " \t\n42\n";
        let tokens = engine(&lexer, source);

        assert!(tokens.is_ok());
        assert_eq!(tokens.unwrap(), vec![Literal(GoLiteral::Integer("42"))]);
    }
}