//! BNF rules internals.
//! Proceed at your own risk!
//!
//! ```
//!                          __    _
//!                     _wr""        "-q__
//!                  _dP                 9m_
//!                _#P                     9#_
//!               d#@                       9#m
//!              d##                         ###
//!             J###                         ###L
//!             {###K                       J###K
//!             ]####K      ___aaa___      J####F
//!         __gmM######_  w#P""   ""9#m  _d#####Mmw__
//!      _g##############mZ_         __g##############m_
//!    _d####M@PPPP@@M#######Mmp gm#########@@PPP9@M####m_
//!   a###""          ,Z"#####@" '######"\g          ""M##m
//!  J#@"             0L  "*##     ##@"  J#              *#K
//!  #"               `#    "_gmwgm_~    dF               `#_
//! 7F                 "#_   ]#####F   _dK                 JE
//! ]                    *m__ ##### __g@"                   F
//!                        "PJ#####LP"
//!  `                       0######_                      '
//!                        _0########_
//!      .               _d#####^#####m__              ,
//!       "*w_________am#####P"   ~9#####mw_________w*"
//!           ""9@#####@M""           ""P@#####@M""
//!
//!
//! ```
#![allow(non_snake_case)]
pub use self::GrammarSymbol::*;
use lang::bnf::{make_lexer, BnfOperator, BnfToken};
use lex::TokensExt;
use std::collections::HashSet;

#[derive(Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Debug, Hash)]
pub enum GrammarSymbol<'a> {
    Terminal(&'a str),
    NonTerminal(&'a str),
}

impl<'a> GrammarSymbol<'a> {
    pub fn to_str(&self) -> String {
        match self {
            Terminal(ref s) => format!("\"{}\"", s),
            NonTerminal(ref s) => format!("<{}>", s),
        }
    }
}

pub trait Epsilon {
    fn epsilon() -> Self;
}

pub trait IsEpsilon {
    /// Is this an empty production symbol, epsilon?
    fn is_epsilon(&self) -> bool;
}

pub trait IsNotEpsilon: IsEpsilon {
    /// Opposite to `IsEpsilon`.
    fn is_not_epsilon(&self) -> bool {
        !self.is_epsilon()
    }
}

impl<'a> Epsilon for &'a str {
    fn epsilon() -> Self {
        ""
    }
}

impl<'a> Epsilon for GrammarSymbol<'a> {
    fn epsilon() -> Self {
        Terminal("")
    }
}

impl<'a> IsEpsilon for GrammarSymbol<'a> {
    fn is_epsilon(&self) -> bool {
        *self == Epsilon::epsilon()
    }
}

impl<'a, 'b> IsEpsilon for &'b GrammarSymbol<'a> {
    fn is_epsilon(&self) -> bool {
        IsEpsilon::is_epsilon(*self)
    }
}

impl<S> IsEpsilon for S
where
    S: AsRef<str>,
{
    fn is_epsilon(&self) -> bool {
        self.as_ref().is_empty()
    }
}

impl<T> IsNotEpsilon for T where T: IsEpsilon {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GrammarProduction<'a>(pub Vec<GrammarSymbol<'a>>);

#[derive(Debug)]
pub struct GrammarRule<'a, 'b> {
    pub name: &'a str,
    /// Alternatives, each in its own sub-vector.
    pub expression: Vec<Vec<GrammarSymbol<'b>>>,
}

impl<'a, 'b> GrammarRule<'a, 'b> {
    pub fn new(name: &'a str) -> Self {
        Self {
            name,
            expression: vec![],
        }
    }

    /// ```bnf
    /// <Rule> ::= <Name> "::=" <Productions>
    /// <Name> ::= <Terminal>
    /// ...
    /// ```
    pub fn from_str(s: &'a str, filename: String) -> Result<GrammarRule<'a, 'a>, &'static str> {
        let lexer = make_lexer();
        let mut tokens = lexer.into_tokens(s, filename).into_raw();

        let name = match tokens.next() {
            Some(BnfToken::NonTerminal(s)) => s,
            _ => Err("NonTerminal expected at the start of the rule.")?,
        };

        if tokens.next() != Some(BnfToken::Operator(BnfOperator::Def)) {
            Err("Equals sign expected after the first nonterminal.")?;
        }

        let mut expression: Vec<Vec<GrammarSymbol>> = vec![];
        let mut prod: Vec<GrammarSymbol> = vec![];
        for token in tokens {
            //println!("{:?}", token);
            match token {
                BnfToken::NonTerminal(s) => prod.push(NonTerminal(s)),
                BnfToken::Terminal(s) => prod.push(Terminal(s)),
                BnfToken::Operator(BnfOperator::Alt) => {
                    expression.push(prod);
                    prod = vec![];
                }
                _ => Err("Unexpected token in the expression part.")?,
            }
        }
        if !prod.is_empty() {
            expression.push(prod);
        }
        Ok(GrammarRule { name, expression })
    }

    pub fn token(&self) -> BnfToken {
        BnfToken::NonTerminal(self.name)
    }

    pub fn symbol(&self) -> GrammarSymbol {
        GrammarSymbol::NonTerminal(self.name)
    }

    pub fn tokens(&self) -> Vec<BnfToken> {
        let mut tokens = vec![
            BnfToken::NonTerminal(self.name),
            BnfToken::Operator(BnfOperator::Def),
        ];

        // tokens.append(&mut self.definitions.tokens());
        {
            let mut first = true;
            for definition in self.expression.iter() {
                if !first {
                    tokens.push(BnfToken::Operator(BnfOperator::Alt));
                }
                first = false;

                // tokens.append(&mut definition.tokens());
                for symbol in definition.iter() {
                    tokens.push(symbol.token());
                }
            }
        }

        tokens
    }
}

#[derive(Debug)]
pub struct Grammar<'a, 'b> {
    pub rules: Vec<GrammarRule<'a, 'b>>,
}

pub fn non_empties<'a, S: AsRef<str>>(iter: impl Iterator<Item = S>) -> impl Iterator<Item = S> {
    iter.filter(|s| !s.as_ref().trim().is_empty())
}

impl<'a, 'b> Grammar<'a, 'b> {
    pub fn new() -> Self {
        Self { rules: Vec::new() }
    }
    pub fn from_str(s: &'a str, filename: String) -> Result<Grammar<'a, 'a>, &'static str> {
        let mut rules = vec![];

        for line in non_empties(s.lines()) {
            rules.push(GrammarRule::from_str(line, filename.clone())?);
        }
        Ok(Grammar { rules })
    }

    pub fn follow(&self, token: GrammarSymbol, start_symbol: GrammarSymbol) -> HashSet<&'b str> {
        let mut set = hash_set!();

        if token == start_symbol {
            set.insert("$");
        }

        for rule in self.rules.iter() {
            for prod in rule.expression.iter() {
                if let Some(i) = prod.iter().position(|&s| s == token) {
                    let (_, follow_symbols) = prod.split_at(i + 1);
                    let mut has_empty = false;

                    if !follow_symbols.is_empty() {
                        let first_beta = self.first(follow_symbols).unwrap();

                        set.extend(first_beta.iter().filter(IsNotEpsilon::is_not_epsilon));

                        if first_beta.contains(Epsilon::epsilon()) {
                            has_empty = true;
                        }
                    } else {
                        has_empty = true;
                    }

                    if has_empty && (NonTerminal(rule.name) != token) {
                        let follow_a = self.follow(NonTerminal(rule.name), start_symbol);
                        for e in follow_a.iter() {
                            set.insert(e);
                        }
                    }
                }
            }
        }
        set
    }

    ///
    /// FIRST set for sequence of productions.
    ///
    /// See `first_unit` and `first_production` for implementation details.
    ///
    /// # Returns
    ///
    /// If grammar is incomplete, i.e. some non-terminals are not defined, an error is returned.
    ///
    pub fn first<G>(&self, symbols: G) -> Result<HashSet<&'b str>, String>
    where
        G: AsRef<[GrammarSymbol<'b>]>,
    {
        self.first_production(symbols.as_ref().into_iter().cloned())
    }

    ///
    /// FIRST set for single symbol.
    ///
    /// First(Λ) = {}
    /// First("c") = {"c"}
    /// First(A) = First(f1) U ... U First(fn)
    ///     where A = f1 | ... | fn
    ///
    pub fn first_unit(&self, symbol: GrammarSymbol<'b>) -> Result<HashSet<&'b str>, String> {
        Ok(if symbol.is_epsilon() {
            hash_set!{ Epsilon::epsilon() }
        } else if let Terminal(c) = symbol {
            hash_set! {c}
        } else if let NonTerminal(A) = symbol {
            let A = self
                .get_rule(A)
                .ok_or_else(|| format!("Invalid grammar! No rule named {}", A))?;

            A.expression
                .iter()
                .map(|f| self.first_production(f.iter().cloned()))
                .collect::<Result<Vec<HashSet<_>>, _>>()?  // early return Err
                .into_iter()
                .flatten() // it could've been flat_map, but Result spoiled the fun
                .collect()
        } else {
            unreachable!();
        })
    }

    /// FIRST set for sequence of productions.
    ///
    /// First(e1 ... em) = { First(e1) U First(e2 ... em) | if e1 ==> Λ
    ///                    { First(e1)                    | otherwise
    pub fn first_production<I>(&self, mut A: I) -> Result<HashSet<&'b str>, String>
    where
        I: Iterator<Item = GrammarSymbol<'b>>,
    {
        Ok(match A.next() {
            None => hash_set!{},
            Some(e) => {
                let mut set = self.first_unit(e)?;
                if set.contains(Epsilon::epsilon()) {
                    set.extend(self.first_production(A)?);
                }
                set
            }
        })
    }

    pub fn get_rule(&self, name: &str) -> Option<&GrammarRule<'a, 'b>> {
        self.rules.iter().find(|r| r.name == name)
    }

    pub fn get_non_terminals(&self) -> HashSet<GrammarSymbol> {
        self.rules.iter().map(|r| NonTerminal(r.name)).collect()
    }

    pub fn get_terminals(&self) -> HashSet<GrammarSymbol> {
        self.rules
            .iter()
            .flat_map(|rule| rule.expression.iter())
            .flat_map(|expr| expr.iter())
            .filter(|sym| sym.is_terminal())
            .cloned()
            .chain(::std::iter::once(Terminal("$")))
            .collect()
    }
}

mod impls {
    use super::*;
    use lex::Token;
    use std::fmt::{Display, Formatter, Result};
    use std::ops::{Deref, DerefMut};

    impl<'a> GrammarSymbol<'a> {
        pub fn is_terminal(&self) -> bool {
            match self {
                Terminal(..) => true,
                NonTerminal(..) => false,
            }
        }

        pub fn is_non_terminal(&self) -> bool {
            !self.is_terminal()
        }

        pub fn token(&self) -> BnfToken {
            match self {
                Terminal(s) => BnfToken::Terminal(s),
                NonTerminal(s) => BnfToken::NonTerminal(s),
            }
        }
    }

    impl<'a, 'b> Display for Grammar<'a, 'b> {
        fn fmt(&self, f: &mut Formatter) -> Result {
            writeln!(f, "BNF Syntax rules:")?;
            for rule in self.rules.iter() {
                writeln!(f, "{}", rule)?;
            }
            Ok(())
        }
    }

    impl<'a, 'b> Display for GrammarRule<'a, 'b> {
        fn fmt(&self, f: &mut Formatter) -> Result {
            let mut tokens = self.tokens().into_iter();
            write!(f, "{}", tokens.next().unwrap().describe())?;
            for t in tokens {
                write!(f, " {}", t.describe())?;
            }
            Ok(())
        }
    }

    impl<'a> Deref for GrammarProduction<'a> {
        type Target = Vec<GrammarSymbol<'a>>;
        fn deref(&self) -> &<Self as Deref>::Target {
            &self.0
        }
    }

    impl<'a> DerefMut for GrammarProduction<'a> {
        fn deref_mut(&mut self) -> &mut <Self as Deref>::Target {
            &mut self.0
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    const FILENAME: &str = "test.bnf";

    #[test]
    fn test_grammar_symbol() {
        let symbol = Terminal("");
        assert!(symbol.is_epsilon());

        let symbol = GrammarSymbol::epsilon();
        assert!(symbol.is_epsilon());

        let symbol = Terminal("abc");
        assert!(!symbol.is_epsilon());

        // in fact, this non-terminal is invalid
        let symbol = NonTerminal("");
        assert!(!symbol.is_epsilon());

        let symbol = NonTerminal("E");
        assert!(!symbol.is_epsilon());
    }

    #[test]
    fn test_bnf_parsing_rule_name() {
        let source = r#"
            <opt-suffix-part> ::= "Sr." | "Jr." | <roman-numeral> | ""
        "#;
        let rule = GrammarRule::from_str(source, FILENAME.into()).unwrap();
        assert_eq!(rule.name, "opt-suffix-part");
    }

    #[test]
    fn test_bnf_parsing_expr() {
        let source = r#"
            <opt-suffix-part> ::= "Sr." | "Jr." <roman-numeral> ""
        "#;
        let rule = GrammarRule::from_str(source, FILENAME.into()).unwrap();
        assert_eq!(
            rule.expression,
            vec![
                vec![GrammarSymbol::Terminal("Sr.")],
                vec![
                    GrammarSymbol::Terminal("Jr."),
                    GrammarSymbol::NonTerminal("roman-numeral"),
                    GrammarSymbol::epsilon()
                ]
            ]
        );
    }

    #[test]
    fn test_first_set() {
        let source = r#"
            <S> ::= "c"<A>"d" | <B><A>
            <A> ::= "a""b" | "a" | ""
            <B> ::= "" | "d"
        "#;
        let grammar = Grammar::from_str(source, FILENAME.into()).unwrap();
        assert_eq!(
            grammar.first(&[NonTerminal("A")]).unwrap(),
            hash_set!["a", ""]
        );
        assert_eq!(
            grammar.first(&[NonTerminal("S")]).unwrap(),
            hash_set!["c", "d", "a", ""]
        );
    }

    #[test]
    fn test_first_set_multiple() {
        let source = r#"
            <S> ::= "c"<A>"d" | <B><A>
            <A> ::= "a""b" | "a" | ""
            <B> ::= "" | "d"
        "#;
        let grammar = Grammar::from_str(source, FILENAME.into()).unwrap();
        assert_eq!(
            grammar
                .first(&[NonTerminal("B"), NonTerminal("A")])
                .unwrap(),
            hash_set!["", "d", "a"]
        );
    }

    #[test]
    fn test_first_set_recursive() {
        let source = r#"
            <E> ::= <T> <E'>
            <E'> ::= "+" <T> <E'> | ""
            <T> ::= <F> <T'>
            <T'> ::= "*" <F> <T'> | ""
            <F> ::= "(" <E> ")" | "id"
        "#;
        let grammar = Grammar::from_str(source, FILENAME.into()).unwrap();
        assert_eq!(
            grammar.first(&[NonTerminal("E'")]).unwrap(),
            hash_set!["+", ""]
        );
        assert_eq!(
            grammar.first(&[NonTerminal("T'")]).unwrap(),
            hash_set!["*", ""]
        );
    }

    #[test]
    fn test_follow_set() {
        let source = r#"
            <E> ::= <T> <E'>
            <E'> ::= "+" <T> <E'> | ""
            <T> ::= <F> <T'>
            <T'> ::= "*" <F> <T'> | ""
            <F> ::= "(" <E> ")" | "id"
        "#;
        let grammar = Grammar::from_str(source, FILENAME.into()).unwrap();
        assert_eq!(
            grammar.follow(NonTerminal("E"), NonTerminal("E")),
            hash_set!["$", ")"]
        );
        assert_eq!(
            grammar.follow(NonTerminal("T"), NonTerminal("E")),
            hash_set!["+", "$", ")"]
        );
    }
}
