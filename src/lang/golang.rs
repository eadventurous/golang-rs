pub use self::GoToken::*;
#[allow(unused)]
use lex::{Lexer, LexerBuilder, Location, MetaResult, Span, Token, TokenMeta, TokensExt};

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

pub fn make_lexer<'a>() -> Lexer<'a, GoToken<'a>> {
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
        // ...
        .add(r"//([^\n]*)\n?", |c| Comment(c.get(1).unwrap().as_str()))
        .add(r"(?s)/\*(.*?)\*/", |c| Comment(c.get(1).unwrap().as_str()))
        // ...
        .add(r"break\b", constant!(Keyword(GoKeyword::Break)))
        .add(r"case\b", constant!(Keyword(GoKeyword::Case)))
        .add(r"defer\b", constant!(Keyword(GoKeyword::Chan)))
        .add(r"else\b", constant!(Keyword(GoKeyword::Const)))
        .add(r"continue\b", constant!(Keyword(GoKeyword::Continue)))
        .add(r"default\b", constant!(Keyword(GoKeyword::Default)))
        .add(r"defer\b", constant!(Keyword(GoKeyword::Defer)))
        .add(r"else\b", constant!(Keyword(GoKeyword::Else)))
        .add(r"fallthroug\b", constant!(Keyword(GoKeyword::Fallthrough)))
        .add(r"for\b", constant!(Keyword(GoKeyword::For)))
        .add(r"func\b", constant!(Keyword(GoKeyword::Func)))
        .add(r"go\b", constant!(Keyword(GoKeyword::Go)))
        .add(r"goto\b", constant!(Keyword(GoKeyword::Goto)))
        .add(r"if\b", constant!(Keyword(GoKeyword::If)))
        .add(r"import\b", constant!(Keyword(GoKeyword::Import)))
        .add(r"interface\b", constant!(Keyword(GoKeyword::Interface)))
        .add(r"map\b", constant!(Keyword(GoKeyword::Map)))
        .add(r"package\b", constant!(Keyword(GoKeyword::Package)))
        .add(r"range\b", constant!(Keyword(GoKeyword::Range)))
        .add(r"return\b", constant!(Keyword(GoKeyword::Return)))
        .add(r"select\b", constant!(Keyword(GoKeyword::Select)))
        .add(r"struct\b", constant!(Keyword(GoKeyword::Struct)))
        .add(r"switch\b", constant!(Keyword(GoKeyword::Switch)))
        .add(r"type\b", constant!(Keyword(GoKeyword::Type)))
        .add(r"var\b", constant!(Keyword(GoKeyword::Var)))
        // ...
        .add(
            r"[[:digit:]]+\.[[:digit:]]*((e|E)(\+|-)?[[:digit:]]*)?i",
            |c| Literal(GoLiteral::Imaginary(c.get(0).unwrap().as_str())),
        ).add(
            r"[[:digit:]]+(e|E)(\+|-)?[[:digit:]]*i",
            |c| Literal(GoLiteral::Imaginary(c.get(0).unwrap().as_str()))
        ).add(
            r"\.[[:digit:]]+((e|E)(\+|-)?[[:digit:]]*)?i",
             |c| Literal(GoLiteral::Imaginary(c.get(0).unwrap().as_str()))
        ).add(
            r"[[:digit:]]+i",
            |c| Literal(GoLiteral::Imaginary(c.get(0).unwrap().as_str())))
        // ...
         .add(
            r"[[:digit:]]+\.[[:digit:]]*((e|E)(\+|-)?[[:digit:]]*)?",
            |c| Literal(GoLiteral::Float(c.get(0).unwrap().as_str()))
        ).add(
            r"[[:digit:]]+(e|E)(\+|-)?[[:digit:]]*",
            |c| Literal(GoLiteral::Float(c.get(0).unwrap().as_str()))
        ).add(
            r"\.[[:digit:]]+((e|E)(\+|-)?[[:digit:]]*)?",
            |c| Literal(GoLiteral::Float(c.get(0).unwrap().as_str())))
        // ...
         .add(
            r"[1-9]+[[:digit:]]*",
            |c| Literal(GoLiteral::Integer(c.get(0).unwrap().as_str()))
        ).add(
            r"0[0-7]*",
            |c| Literal(GoLiteral::Integer(c.get(0).unwrap().as_str()))
        ).add(
            r"0(x|X)[[:xdigit:]]+",
            |c| Literal(GoLiteral::Integer(c.get(0).unwrap().as_str()))
        )
        // ...
         .add(r"\+=", constant!(Operator(GoOperator::AddAssign)))
         .add(r"-=", constant!(Operator(GoOperator::SubAssign)))
         .add(r"\*=", constant!(Operator(GoOperator::MulAssign)))
         .add(r"/=", constant!(Operator(GoOperator::QuoAssign)))
         .add(r"%=", constant!(Operator(GoOperator::RemAssign)))
         .add(r"&=", constant!(Operator(GoOperator::AndAssign)))
         .add(r"\|=", constant!(Operator(GoOperator::OrAssign)))
         .add(r"\^=", constant!(Operator(GoOperator::XorAssign)))
         .add(r"<<=", constant!(Operator(GoOperator::ShlAssign)))
         .add(r">>=", constant!(Operator(GoOperator::ShrAssign)))
         .add(r"&\^=", constant!(Operator(GoOperator::AndNotAssign)))
         .add(r"&&", constant!(Operator(GoOperator::LAnd)))
         .add(r"\|\|", constant!(Operator(GoOperator::LOr)))
         .add(r"<-", constant!(Operator(GoOperator::Arrow)))
         .add(r"\+\+", constant!(Operator(GoOperator::Inc)))
         .add(r"--", constant!(Operator(GoOperator::Dec)))
         .add(r"!=", constant!(Operator(GoOperator::NEq)))
         .add(r"<=", constant!(Operator(GoOperator::LEq)))
         .add(r">=", constant!(Operator(GoOperator::GEq)))
         .add(r":=", constant!(Operator(GoOperator::Define)))
         .add(r"\.\.\.", constant!(Operator(GoOperator::Ellipsis)))
         .add(r"\(", constant!(Operator(GoOperator::LParen)))
         .add(r"\[", constant!(Operator(GoOperator::LBrack)))
         .add(r"\{", constant!(Operator(GoOperator::LBrace)))
         .add(r",", constant!(Operator(GoOperator::Comma)))
         .add(r"\.", constant!(Operator(GoOperator::Period)))
         .add(r"\)", constant!(Operator(GoOperator::RParen)))
         .add(r"\]", constant!(Operator(GoOperator::RBrack)))
         .add(r"\}", constant!(Operator(GoOperator::RBrace)))
         .add(r";", constant!(Operator(GoOperator::Semicolon)))
         .add(r":", constant!(Operator(GoOperator::Colon)))
         .add(r"==", constant!(Operator(GoOperator::Eql)))
         .add(r"<", constant!(Operator(GoOperator::Lss)))
         .add(r">", constant!(Operator(GoOperator::Gtr)))
         .add(r"=", constant!(Operator(GoOperator::Assign)))
         .add(r"!", constant!(Operator(GoOperator::Not)))
         .add(r"&\^", constant!(Operator(GoOperator::AndNot)))
         .add(r"&", constant!(Operator(GoOperator::And)))
         .add(r"\|", constant!(Operator(GoOperator::Or)))
         .add(r"\^", constant!(Operator(GoOperator::Xor)))
         .add(r"<<", constant!(Operator(GoOperator::Shl)))
         .add(r">>", constant!(Operator(GoOperator::Shr)))
         .add(r"\+", constant!(Operator(GoOperator::Add)))
         .add(r"-", constant!(Operator(GoOperator::Sub)))
         .add(r"\*", constant!(Operator(GoOperator::Mul)))
         .add(r"/", constant!(Operator(GoOperator::Quo)))
         .add(r"%", constant!(Operator(GoOperator::Rem)))
        // ...
         .add(rune, |c| {
            GoToken::Literal(GoLiteral::Rune(c.get(1).unwrap().as_str()))
        }).add(raw_string, |c| {
            GoToken::Literal(GoLiteral::RawString(c.get(1).unwrap().as_str()))
        }).add(interpreted_string, |c| {
            GoToken::Literal(GoLiteral::InterpretedString(c.get(1).unwrap().as_str()))
        }).add(r"(\p{L}|_)(\p{L}|_|\p{Nd})*", |c| {
            Ident(c.get(0).unwrap().as_str())
        }).build()
}

impl<'a> Token<'a> for GoToken<'a> {
    fn describe(&self) -> String {
        match *self {
            GoToken::Ident(ref id) => id.to_string(),
            GoToken::Keyword(ref kw) => format!("{:?}", kw),
            _ => format!("{:?}", self),
        }
    }
    /// used for grammar symbol matching at the syntax analysis phaze
    fn descriptor(&self) -> &'static str {
        match *self {
            Ident(_) => "identifier",
            Keyword(ref kw) => match kw {
                GoKeyword::Break => "break",
                GoKeyword::Default => "default",
                GoKeyword::Func => "func",
                GoKeyword::Interface => "interface",
                GoKeyword::Select => "select",
                GoKeyword::Case => "case",
                GoKeyword::Defer => "defer",
                GoKeyword::Go => "go",
                GoKeyword::Map => "map",
                GoKeyword::Struct => "struct",
                GoKeyword::Chan => "chan",
                GoKeyword::Else => "else",
                GoKeyword::Goto => "goto",
                GoKeyword::Package => "package",
                GoKeyword::Switch => "switch",
                GoKeyword::Const => "const",
                GoKeyword::Fallthrough => "fallthrough",
                GoKeyword::If => "if",
                GoKeyword::Range => "range",
                GoKeyword::Type => "type",
                GoKeyword::Continue => "continue",
                GoKeyword::For => "for",
                GoKeyword::Import => "import",
                GoKeyword::Return => "return",
                GoKeyword::Var => "var",
            },
            Operator(ref op) => match op {
                GoOperator::Add => "+",
                GoOperator::Sub => "-",
                GoOperator::Mul => "*",
                GoOperator::Quo => "/",
                GoOperator::Rem => "%",

                GoOperator::And => "&",
                GoOperator::Or => "|",
                GoOperator::Xor => "^",
                GoOperator::Shl => "<<",
                GoOperator::Shr => ">>",
                GoOperator::AndNot => "&^",

                GoOperator::AddAssign => "+=",
                GoOperator::SubAssign => "-=",
                GoOperator::QuoAssign => "/=",
                GoOperator::RemAssign => "%=",
                GoOperator::MulAssign => "*=",

                GoOperator::AndAssign => "&=",
                GoOperator::OrAssign => "|=",
                GoOperator::XorAssign => "^=",
                GoOperator::ShlAssign => "<<=",
                GoOperator::ShrAssign => ">>=",
                GoOperator::AndNotAssign => "&^=",

                GoOperator::LAnd => "&&",
                GoOperator::LOr => "||",
                GoOperator::Arrow => "<-",
                GoOperator::Inc => "++",
                GoOperator::Dec => "--",

                GoOperator::Eql => "==",
                GoOperator::Lss => "<",
                GoOperator::Gtr => ">",
                GoOperator::Assign => "=",
                GoOperator::Not => "!",

                GoOperator::NEq => "!=",
                GoOperator::LEq => "<=",
                GoOperator::GEq => ">=",
                GoOperator::Define => ":=",
                GoOperator::Ellipsis => "...",

                GoOperator::LParen => "(",
                GoOperator::LBrack => "[",
                GoOperator::LBrace => "{",

                GoOperator::Comma => ",",
                GoOperator::Period => ".",

                GoOperator::RParen => ")",
                GoOperator::RBrack => "]",
                GoOperator::RBrace => "}",

                GoOperator::Semicolon => ";",
                GoOperator::Colon => ":",
            },
            Literal(GoLiteral::RawString(..)) | Literal(GoLiteral::InterpretedString(..)) => {
                "string_lit"
            }
            Literal(GoLiteral::Integer(..)) => "int_lit",
            Literal(GoLiteral::Float(..)) => "float_lit",
            Literal(GoLiteral::Imaginary(..)) => "imaginary_lit",
            Literal(GoLiteral::Rune(..)) => "rune_lit",
            Comment(_) => "comment",
        }
    }
}

pub fn drop_comments<'a, I>(iter: I) -> DropComments<I>
where
    I: Iterator<Item = MetaResult<'a, GoToken<'a>>>,
{
    DropComments { inner: iter }
}

pub struct DropComments<I> {
    inner: I,
}

impl<'a, I> Iterator for DropComments<I>
where
    I: Iterator<Item = MetaResult<'a, GoToken<'a>>>,
{
    type Item = MetaResult<'a, GoToken<'a>>;

    fn next(&mut self) -> Option<<Self as Iterator>::Item> {
        let mut next = self.inner.next();
        while let Some(Ok(TokenMeta {
            token: GoToken::Comment(_),
            ..
        })) = next
        {
            next = self.inner.next();
        }
        next
    }
}

/// Insert missing optional semicolons into the token stream.
///
/// The following text is taken from The Go Programming Language Specification on [semicolons].
///
/// # Semicolons
///
/// The formal grammar uses semicolons ";" as terminators in a number of productions. Go programs
/// may omit most of these semicolons using the following two rules:
///
/// 1. When the input is broken into tokens, a semicolon is automatically inserted into the token
/// stream immediately after a line's final token if that token is
///     * an identifier
///     * an integer, floating-point, imaginary, rune, or string literal
///     * one of the keywords `break`, `continue`, `fallthrough`, or `return`
///     * one of the operators and punctuation `++`, `--`, `)`, `]`, or `}`
/// 2. To allow complex statements to occupy a single line, a semicolon may be omitted before a
/// closing "`)`" or "`}`".
///
/// [semicolons]: https://golang.org/ref/spec#Semicolons
pub fn necessary_semicolon<'a, I>(iter: I) -> NecessarySemicolon<'a, I>
where
    I: Iterator<Item = MetaResult<'a, GoToken<'a>>>,
{
    NecessarySemicolon {
        inner: iter,
        poisoned: false,
        pending: None,
        last: None,
    }
}

pub struct NecessarySemicolon<'a, I> {
    inner: I,
    poisoned: bool,
    /// If the last token was implicit semicolon, this should contain the next token to return.
    pending: Option<TokenMeta<GoToken<'a>>>,
    last: Option<TokenMeta<GoToken<'a>>>,
}

impl<'a, I> NecessarySemicolon<'a, I> {
    fn same_line(&self, other: &TokenMeta<GoToken<'a>>) -> bool {
        match self.last {
            Some(TokenMeta { ref span, .. }) => span.same_line(&other.span),
            None => true,
        }
    }

    fn new_line(&self, other: &TokenMeta<GoToken<'a>>) -> bool {
        !self.same_line(other)
    }

    fn insert_semicolon(after: &TokenMeta<GoToken<'a>>) -> TokenMeta<GoToken<'a>> {
        // semicolon spans directly after last token
        let last = after.span.end;
        let loc = Location::new(last.line, last.column + 1, last.absolute + 1);

        TokenMeta {
            span: Span::from_location(loc),
            token: GoToken::Operator(GoOperator::Semicolon),
            implicit: true,
        }
    }

    fn recover_after_semicolon(&mut self) -> Option<TokenMeta<GoToken<'a>>> {
        match self.pending.take() {
            Some(meta) => Some(meta),
            None => None,
        }
    }

    fn process(&mut self, meta: TokenMeta<GoToken<'a>>) -> TokenMeta<GoToken<'a>> {
        /* rule one */
        if self.new_line(&meta) {
            match self
                .last
                .take()
                .filter(Self::rule_1)
                .as_ref()
                .map(Self::insert_semicolon)
            {
                Some(semi) => {
                    self.pending = Some(meta);
                    semi
                }
                None => meta,
            }
        } else if false {
            /* rule two */
            // ???
            meta
        } else {
            meta
        }
    }

    fn rule_1(token: &TokenMeta<GoToken<'a>>) -> bool {
        match token.token {
            Ident(..)
            | Literal(..)
            | Keyword(GoKeyword::Continue)
            | Keyword(GoKeyword::Break)
            | Keyword(GoKeyword::Fallthrough)
            | Keyword(GoKeyword::Return)
            | Operator(GoOperator::Inc)
            | Operator(GoOperator::Dec)
            | Operator(GoOperator::RParen)
            | Operator(GoOperator::RBrace)
            | Operator(GoOperator::RBrack) => true,
            _ => false,
        }
    }
}

impl<'a, I> Iterator for NecessarySemicolon<'a, I>
where
    I: Iterator<Item = MetaResult<'a, GoToken<'a>>>,
{
    type Item = MetaResult<'a, GoToken<'a>>;

    fn next(&mut self) -> Option<<Self as Iterator>::Item> {
        if self.poisoned {
            return None;
        }

        let token = {
            match self.recover_after_semicolon() {
                Some(meta) => meta,
                None => {
                    match self.inner.next() {
                        Some(Ok(meta)) => self.process(meta),
                        // the last semicolon
                        None => {
                            return self
                                .last
                                .take()
                                .filter(Self::rule_1)
                                .as_ref()
                                .map(Self::insert_semicolon)
                                .map(Ok)
                        }
                        // pass through
                        next @ Some(Err(..)) => {
                            self.poisoned = true;
                            self.last = None;
                            self.pending = None;
                            return next;
                        }
                    }
                }
            }
        };
        self.last = Some(token.clone());
        Some(Ok(token))
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use lex::{next, token};

    macro_rules! must_not_match_token {
        ($lexer:expr, $source:expr, $tok:pat) => {
            match $lexer.tokens($source, "must-not-match".into()).next() {
                Some(Ok($crate::lex::TokenMeta { token: $tok, .. })) => {
                    panic!("Token must not match!")
                }
                _ => {}
            }
        };
    }

    const FILENAME: &str = "test.bnf";

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

            r"vars", // legal: starts with keyword substring
            r"ifelse",
        ];
        let illegal_id = [
            r"6a", // illegal: can't start with digit
            r".a", // illegal: can't start with dot

            r"if", // illegal: is a keyword
            r"var",

        ];
        for id in valid_id.into_iter() {
            assert_eq!(token(next(&lexer, id)), GoToken::Ident(&id));
        }
        for id in illegal_id.into_iter() {
            must_not_match_token!(lexer, id, GoToken::Ident(_));
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
            r"e6i",  // illegal: can't start with i
            r"..6i", // illegal: too many dots
            r"82",   // illegal: it is integer
            r"4.5",  // illegal: it is float
            r"i",    //illegal: can't start with i
        ];
        for imaginary in valid_imaginary.into_iter() {
            assert_eq!(
                token(next(&lexer, imaginary)),
                GoToken::Literal(GoLiteral::Imaginary(&imaginary))
            );
        }
        for imaginary in illegal_imaginary.into_iter() {
            must_not_match_token!(lexer, imaginary, GoToken::Literal(GoLiteral::Imaginary(_)));
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
            r"e6",  // illegal: can't start with exponent
            r"..6", // illegal: too many dots
            r"82",  // illegal: it is integer
        ];
        for float in valid_floats.into_iter() {
            assert_eq!(
                token(next(&lexer, float)),
                GoToken::Literal(GoLiteral::Float(&float))
            );
        }
        for float in illegal_floats.into_iter() {
            must_not_match_token!(lexer, float, Literal(GoLiteral::Float(_)));
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
            r"'\''", // rune literal containing single quote character
        ];
        let illegal_runes = [
            r"'aa'",  // illegal: too many characters
            r"'\xa'", // illegal: too few hexadecimal digits
            r"'\0'",  // illegal: too few octal digits
                      // Regexp-based lexer cannot detect surrogate half,
                      // r"'\uDFFF'",     // illegal: surrogate half
                      // ...nor it is capable of understanding Unicode code points.
                      // r"'\U00110000'", // illegal: invalid Unicode code point
        ];
        for rune in valid_runes.into_iter() {
            assert_eq!(
                token(next(&lexer, rune)),
                GoToken::Literal(GoLiteral::Rune(&rune[1..rune.len() - 1]))
            );
        }
        for rune in illegal_runes.into_iter() {
            assert!(next(&lexer, rune).unwrap().is_err());
        }
    }

    #[test]
    fn test_string_lit() {
        let lexer = make_lexer();

        let raw_strings = [
            r"`abc`", // same as "abc"
            r"`\n
\n`", // same as "\\n\n\\n"
        ];
        let interpreted_strings = [
            r#""\n""#,
            r#""\"""#, // same as `"`
            r#""Hello, world!\n""#,
            r#""日本語""#,
            r#""\u65e5本\U00008a9e""#,
            r#""\xff\u00FF""#,
        ];

        for s in raw_strings.into_iter() {
            assert_eq!(
                token(next(&lexer, s)),
                GoToken::Literal(GoLiteral::RawString(&s[1..s.len() - 1]))
            );
        }

        for s in interpreted_strings.into_iter() {
            assert_eq!(
                token(next(&lexer, s)),
                GoToken::Literal(GoLiteral::InterpretedString(&s[1..s.len() - 1]))
            );
        }
    }

    #[test]
    fn test_white_space() {
        let lexer = make_lexer();
        let source = " \t\n42\n";
        let tokens = lexer
            .into_tokens(source, FILENAME.into())
            .into_raw()
            .collect::<Vec<_>>();

        assert_eq!(vec![Literal(GoLiteral::Integer("42"))], tokens);
    }

    #[test]
    fn test_semicolon() {
        let lexer = make_lexer();
        let source = "i++\nj";
        let tokens = necessary_semicolon(drop_comments(lexer.into_tokens(source, FILENAME.into())))
            .into_raw()
            .collect::<Vec<_>>();

        assert_eq!(
            tokens,
            [
                Ident("i"),
                Operator(GoOperator::Inc),
                Operator(GoOperator::Semicolon),
                Ident("j"),
                Operator(GoOperator::Semicolon),
            ]
        );
    }

    #[test]
    fn test_semicolon_eof() {
        let source = "package main";
        let tokens = necessary_semicolon(make_lexer().into_tokens(source, FILENAME.into()))
            .into_raw()
            .collect::<Vec<_>>();

        assert_eq!(
            tokens,
            [
                Keyword(GoKeyword::Package),
                Ident("main"),
                Operator(GoOperator::Semicolon),
            ]
        );
    }

    #[test]
    fn test_semicolon_empty() {
        let source = "";
        let mut tokens = necessary_semicolon(make_lexer().into_tokens(source, FILENAME.into()));
        assert!(tokens.next().is_none());
    }
}
