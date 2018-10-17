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
    pub fn new(name: &'a str) -> Self {
        Rule {
            name,
            definitions: DefinitionList(vec![]),
        }
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
    use lex::{MetaResult, SimpleErrorBytes, Token, TokenMeta};
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

        pub fn parse<S>(
            source: &'a str,
            filename: &'a str,
        ) -> Result<Syntax<'a>, SimpleErrorBytes> {
            let mut rules = vec![];

            for line in non_empties(source.lines()) {
                rules.push(Self::parse_rule(line, filename)?);
            }

            Ok(Syntax { rules })
        }

        pub fn parse_rule(
            source: &'a str,
            _filename: &'a str,
        ) -> Result<Rule<'a>, SimpleErrorBytes> {
            let iter = make_lexer().tokens(source);
            let mut this = Parser::new(source, iter);

            let name = this.expect_non_terminal()?;
            this.expect_exact(Operator(Def))?;
            this.parse_alternatives(None)?;

            Ok(Rule::new(name))
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
                        // def.push(self.parse_optional());
                    }
                    Repeat(Start) => {
                        // def.push(self.parse_repeat());
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
            match self.current() {
                Some(Err(e)) => Err(e.clone().into()),
                Some(Ok(..)) | None => Ok(DefinitionList(definitions)),
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
                        .unwrap_or(Default::default());
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

    const FILENAME: &str = "<test.bnf>";

    #[test]
    fn test_parse_expectation() {
        let source = r#"??? ::= <A> "B" <C>"#;
        let filename = "invalid.txt";
        let result = Parser::parse_rule(source, filename);
        assert!(result.is_err());
        println!("{:?}", result.err().unwrap())
    }

    #[test]
    fn test_parse_empty() {
        let res = Parser::parse_rule("", FILENAME);
        assert!(res.is_err());

        let err = res.err().unwrap();
        println!("AAAAAAA: {:?}", err);
        let err: ::lex::Error<_> = err.into();
        let err = err.source("").filename(FILENAME);
        println!("AAAAAAA:\n{}", err);
    }

    #[test]
    fn test_parse_epsilon() {
        let source = "<A> ::= ";
        let res = Parser::parse_rule(source, FILENAME);
        assert!(res.is_ok());

        let rule = res.unwrap();
        assert_eq!("A", rule.name);
        assert_eq!(rule.definitions.0, vec![]);
        //        println!("BBBBBBB: {:?}", err);
        //        let err: ::lex::Error<_> = err.into();
        //        let err = err.source(source).filename(FILENAME);
        //        println!("BBBBBBB\n{}", err);
    }
}
