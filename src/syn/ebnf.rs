//! # EBNF syntax parser and converter

use lang::ebnf::*;
use lex::MetaResult;

pub struct Syntax<'a> {
    rules: Vec<Rule<'a>>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Rule<'a> {
    name: &'a str,
    definitions: DefinitionList<'a>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DefinitionList<'a>(pub Vec<Definition<'a>>);

/// Syntactic definitions are separated by one of '|', '/', '!'.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Definition<'a>(pub Vec<Primary<'a>>);
pub type Alternative<'a> = Definition<'a>;

/// Syntactic terms are separated by comma ','.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Primary<'a> {
    Optional(DefinitionList<'a>),
    Repeated(DefinitionList<'a>),
    Grouped(DefinitionList<'a>),
    Terminal(&'a str),
    NonTerminal(&'a str),
    Empty,
}

/// To be a little bit more consistent with ISO standard on EBNF.
pub type Term<'a> = Primary<'a>;
pub type Factor<'a> = Primary<'a>;

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Nesting {
    Optional,
    Repeated,
    Grouped,
}

impl<'a> Syntax<'a> {
    /// 1. Convert every repetition `{ E }` to a fresh non-terminal `X` and add `X = eps | X E`.
    fn rule_1(&self) {}

    /// 2. Convert every option `[ E ]` to a fresh non-terminal `X` and add `X = eps | E`.
    /// (We can convert `X = A [ E ] B` to `X = A E B | A B`.)
    fn rule_2(&self) {}

    /// 3. Convert every group `( E )` to a fresh non-terminal `X` and add `X = E`.
    fn rule_3(&self) {}
}

impl<'a> Rule<'a> {
    pub fn new(name: &'a str, definitions: DefinitionList<'a>) -> Self {
        Rule { name, definitions }
    }

    pub fn tokens(&self) -> Vec<EbnfToken<'a>> {
        let mut tokens = vec![EbnfToken::NonTerminal(self.name), EbnfToken::Operator(Def)];

        tokens.append(&mut self.definitions.tokens());

        tokens
    }
}

pub struct Parser<'a> {
    /// Source text
    source: &'a str,
    /// Current token.
    t: Option<MetaResult<'a, EbnfToken<'a>>>,
    //    /// Index of current token.
    //    i: usize,
    /// Iterator over tokens stream.
    iter: ::lex::Tokens<'a, EbnfToken<'a>>,
}

mod impls {
    use super::*;
    use lex::{MetaResult, SimpleErrorBytes, Span, Token, TokenMeta};
    use std::fmt::{self, Display, Formatter};
    use syn::bnf::non_empties;

    impl<'a> Display for Rule<'a> {
        fn fmt(&self, f: &mut Formatter) -> fmt::Result {
            let mut tokens = self.tokens().into_iter();
            write!(f, "{}", tokens.next().unwrap().describe())?;
            for t in tokens {
                write!(f, " {}", t.describe())?;
            }
            Ok(())
        }
    }

    impl<'a> DefinitionList<'a> {
        pub fn tokens(&self) -> Vec<EbnfToken<'a>> {
            let mut tokens = vec![];

            let mut first = true;
            for d in &self.0 {
                if !first {
                    tokens.push(Operator(Alt));
                }
                first = false;

                tokens.append(&mut d.tokens())
            }

            tokens
        }
    }

    impl<'a> Definition<'a> {
        pub fn tokens(&self) -> Vec<EbnfToken<'a>> {
            let mut tokens = vec![];

            for p in &self.0 {
                tokens.append(&mut p.tokens());
            }

            tokens
        }
    }

    impl<'a> Primary<'a> {
        pub fn tokens(&self) -> Vec<EbnfToken<'a>> {
            let mut tokens = vec![];
            match *self {
                Primary::Optional(ref list) => {
                    tokens.push(Optional(Start));
                    tokens.append(&mut list.tokens());
                    tokens.push(Optional(End));
                }
                Primary::Repeated(ref list) => {
                    tokens.push(Repeat(Start));
                    tokens.append(&mut list.tokens());
                    tokens.push(Repeat(End));
                }
                Primary::Grouped(ref list) => {
                    tokens.push(Group(Start));
                    tokens.append(&mut list.tokens());
                    tokens.push(Group(End));
                }
                Primary::Terminal(t) => {
                    tokens.push(Terminal(t));
                }
                Primary::NonTerminal(t) => {
                    tokens.push(NonTerminal(t));
                }
                Primary::Empty => {}
            }
            tokens
        }
    }

    type EbnfTokens<'a> = ::lex::Tokens<'a, EbnfToken<'a>>;

    impl Nesting {
        fn expected(&self) -> &'static str {
            match *self {
                Nesting::Grouped => ")",
                Nesting::Optional => "]",
                Nesting::Repeated => "}",
            }
        }
    }

    impl<'a> Parser<'a> {
        fn new(source: &'a str, iter: EbnfTokens<'a>) -> Self {
            Parser {
                source,
                t: None,
                iter,
            }
        }

        pub fn parse(source: &'a str) -> Result<Syntax<'a>, SimpleErrorBytes> {
            let mut rules = vec![];

            for line in non_empties(source.lines()) {
                rules.push(Self::parse_rule(line)?);
            }

            Ok(Syntax { rules })
        }

        pub fn parse_rule(source: &'a str) -> Result<Rule<'a>, SimpleErrorBytes> {
            let iter = make_lexer().tokens(source);
            let mut this = Parser::new(source, iter);

            let name = this.expect_non_terminal()?;
            this.expect_exact(Operator(Def))?;
            let definitions = this.parse_alternatives(None)?;

            Ok(Rule::new(name, definitions))
        }

        fn parse_alternatives(
            &mut self,
            nesting: Option<Nesting>,
        ) -> Result<DefinitionList<'a>, SimpleErrorBytes> {
            let mut definitions = vec![];
            let mut def = vec![];

            while let Some(Ok(meta)) = self.next() {
                match meta.token.clone() {
                    Terminal(t) => {
                        def.push(Primary::Terminal(t));
                    }
                    NonTerminal(t) => {
                        def.push(Primary::NonTerminal(t));
                    }
                    Operator(Alt) => {
                        definitions.push(Definition(def));
                        def = vec![];
                    }
                    Group(Start) => {
                        let list = self.parse_alternatives(Some(Nesting::Grouped))?;
                        def.push(Primary::Grouped(list));
                    }
                    Optional(Start) => {
                        let list = self.parse_alternatives(Some(Nesting::Optional))?;
                        def.push(Primary::Optional(list));
                    }
                    Repeat(Start) => {
                        let list = self.parse_alternatives(Some(Nesting::Repeated))?;
                        def.push(Primary::Repeated(list));
                    }
                    Group(End) if Some(Nesting::Grouped) == nesting => break,
                    Optional(End) if Some(Nesting::Optional) == nesting => break,
                    Repeat(End) if Some(Nesting::Repeated) == nesting => break,
                    Group(End) | Optional(End) | Repeat(End) => {
                        Err(match nesting {
                            Some(ref nesting) => self.error_expected(nesting.expected()),
                            None => self.error_expected(
                                "none of enclosing parenthesis at top level definition",
                            ),
                        })?;
                    }
                    Operator(Def) => {
                        Err(self.error_expected("anything but ::= operator!"))?;
                    }
                }
            }
            definitions.push(Definition(def));
            match (self.current(), nesting) {
                (Some(Err(e)), _) => Err(e.clone().into()),
                (Some(Ok(..)), _) | (None, None) => {
                    // no more tokens nor nesting
                    Ok(DefinitionList(definitions))
                }
                // no more tokens but nested groups left opened.
                (None, Some(ref nesting)) => Err(self.error_expected(nesting.expected())),
            }
        }

        fn current(&self) -> Option<MetaResult<'a, EbnfToken<'a>>> {
            self.t.clone()
        }

        fn next(&mut self) -> Option<MetaResult<'a, EbnfToken<'a>>> {
            let result = self.iter.next();
            self.t = result;
            self.current()
        }

        fn expect_non_terminal(&mut self) -> Result<&'a str, SimpleErrorBytes> {
            match self.next() {
                Some(Ok(TokenMeta {
                    token: NonTerminal(t),
                    ..
                })) => Ok(t),
                _ => Err(self.error_expected("non-terminal.")),
            }
        }

        fn expect_exact(&mut self, tok: EbnfToken<'a>) -> Result<(), SimpleErrorBytes> {
            match self.next() {
                Some(Ok(TokenMeta { token, .. })) if tok == token => Ok(()),
                _ => Err(self.error_expected(tok.descriptor())),
            }
        }

        fn error_expected(&self, expectation: &str) -> SimpleErrorBytes {
            let description = format!("Expected {}.", expectation);
            match self.current() {
                Some(Ok(meta)) => Into::<SimpleErrorBytes>::into(meta.clone()),
                Some(Err(e)) => Into::<SimpleErrorBytes>::into(e.clone()),
                None => {
                    let span = self
                        .current()
                        .clone()
                        .and_then(|x| x.ok())
                        .map(|t| t.span)
                        .or_else(|| Span::over(self.source))
                        .unwrap_or_default();
                    SimpleErrorBytes {
                        span,
                        description: None,
                    }
                }
            }.description(Some(description))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use lex::Error;

    const FILENAME: &str = "<test.bnf>";

    #[test]
    fn test_parse_expectation() {
        let source = r#"??? ::= <A> "B" <C>"#;
        let result = Parser::parse_rule(source);
        assert!(result.is_err());
        // println!("{:?}", result.err().unwrap())
    }

    #[test]
    fn test_parse_empty() {
        let source = " ";
        let res = Parser::parse_rule(source);
        assert!(res.is_err());

        let err = res.err().unwrap();
        let err: Error<_> = err.into();
        let err = err.source(source).filename(FILENAME);
        // println!("AAAAAAA: {:?}", err);
        // println!("AAAAAAA:\n{}", err);
        let _ = err;
    }

    #[test]
    fn test_parse_no_def() {
        let source = "<A> <AC/DC> <EFG> ::= \"123\" ";
        let res = Parser::parse_rule(source);
        assert!(res.is_err());

        let err: Error<_> = res.err().unwrap().into();
        let err = err.source(source).filename(FILENAME);
        // println!("AAA\n{:?}", err);
        // println!("AAA\n{}", err);
        let _ = err;
    }

    #[test]
    fn test_parse_epsilon() {
        let source = "<A> ::= ";
        let res = Parser::parse_rule(source);
        assert!(res.is_ok());

        let rule = res.unwrap();
        assert_eq!("A", rule.name);
        assert_eq!(rule.definitions.0, vec![Definition(vec![])]);
    }

    #[test]
    fn test_parse_simple_product() {
        let source = r#" <A> ::= <B> "C" "#;
        let res = Parser::parse_rule(source);
        assert!(res.is_ok());

        let rule = res.unwrap();
        assert_eq!("A", rule.name);
        assert_eq!(
            rule.definitions.0,
            vec![Definition(vec![
                Primary::NonTerminal("B"),
                Primary::Terminal("C")
            ])]
        );
    }

    #[test]
    fn test_parse_alternatives() {
        let source = r#" <A> ::= <B> | "#;
        let res = Parser::parse_rule(source);
        assert!(res.is_ok());

        let rule = res.unwrap();
        assert_eq!(rule.name, "A");
        assert_eq!(
            rule.definitions.0,
            vec![
                Definition(vec![Primary::NonTerminal("B")]),
                Definition(vec![])
            ]
        );
    }

    #[test]
    fn test_parse_group() {
        let source = r#" <A> ::= <B> ("c" | <D> <E> | "f") | "g" "#;
        let res = Parser::parse_rule(source);
        assert!(res.is_ok());

        let rule = res.unwrap();
        assert_eq!(rule.name, "A");
        assert_eq!(
            rule.definitions.0,
            vec![
                Definition(vec![
                    Primary::NonTerminal("B"),
                    Primary::Grouped(DefinitionList(vec![
                        Definition(vec![Primary::Terminal("c")]),
                        Definition(vec![Primary::NonTerminal("D"), Primary::NonTerminal("E")]),
                        Definition(vec![Primary::Terminal("f")])
                    ]))
                ]),
                Definition(vec![Primary::Terminal("g")])
            ]
        );
    }

    #[test]
    fn test_parse_group_unclosed() {
        let source = r#" <A> ::= <B> ( "c" | "#;
        let res = Parser::parse_rule(source);
        assert!(res.is_err());

        let source = r#" <A> ::= <B> [ "c" | "#;
        let res = Parser::parse_rule(source);
        assert!(res.is_err());

        let source = r#" <A> ::= <B> { "c" | "#;
        let res = Parser::parse_rule(source);
        assert!(res.is_err());
    }

    #[test]
    fn test_parse_unexpected_close() {
        let source = r#" <A> ::= ) "#;
        let res = Parser::parse_rule(source);
        assert!(res.is_err());
        // println!("EEE {:?}", res);
    }

    #[test]
    fn test_parse_unexpected_close_another() {
        let source = r#" <A> ::= { [ "b" } "#;
        let res = Parser::parse_rule(source);
        assert!(res.is_err());
        // println!("EEE {:?}", res);
    }

    #[test]
    fn test_parse_deep_nesting() {
        let source = r#" <A> ::= { "b" ([<C>] <D> | "e" {"e"} ) } "#;
        let res = Parser::parse_rule(source);
        assert!(res.is_ok());
    }

    /// # Syntax

    #[test]
    fn test_whole_syntax() {
        let source = r#"
            <A> ::= "d" [ <B> ]
            <B> ::= "c" <A> | <D>

            <D> ::= "e" { "f" <A> }
        "#;
        let res = Parser::parse(source);
        assert!(res.is_ok());

        let syntax = res.unwrap();
        assert_eq!(
            syntax.rules,
            vec![
                Rule::new(
                    "A",
                    DefinitionList(vec![Definition(vec![
                        Primary::Terminal("d"),
                        Primary::Optional(DefinitionList(vec![Definition(vec![
                            Primary::NonTerminal("B")
                        ])]))
                    ])])
                ),
                Rule::new(
                    "B",
                    DefinitionList(vec![
                        Definition(vec![Primary::Terminal("c"), Primary::NonTerminal("A")]),
                        Definition(vec![Primary::NonTerminal("D")])
                    ])
                ),
                Rule::new(
                    "D",
                    DefinitionList(vec![Definition(vec![
                        Primary::Terminal("e"),
                        Primary::Repeated(DefinitionList(vec![Definition(vec![
                            Primary::Terminal("f"),
                            Primary::NonTerminal("A"),
                        ])]))
                    ])])
                )
            ]
        );
    }
}
