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
        let s = match self.clone() {
            Terminal(s) => s,
            NonTerminal(s) => s,
        };
        s.to_string()
    }
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

impl<'a> IsEpsilon for GrammarSymbol<'a> {
    fn is_epsilon(&self) -> bool {
        *self == Terminal("")
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

#[derive(Clone, Debug)]
pub struct GrammarProduction<'a>(pub GrammarSymbol<'a>, pub Vec<GrammarSymbol<'a>>);

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

    pub fn non_terminal(&self) -> BnfToken {
        BnfToken::NonTerminal(self.name)
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
                        let first_beta = self.first(follow_symbols.to_vec());

                        set.extend(first_beta.iter().filter(IsNotEpsilon::is_not_epsilon));

                        if first_beta.contains(&"") {
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

    pub fn first(&self, tokens: Vec<GrammarSymbol<'b>>) -> HashSet<&'b str> {
        let mut set = hash_set!{};

        for token in tokens {
            let mut x_set = hash_set!{};

            match token {
                Terminal(s) => {
                    x_set.insert(s);
                }
                NonTerminal(name) => {
                    let rule = self
                        .get_rule(name)
                        .unwrap_or_else(|| panic!("Invalid grammar! No rule named {}", name));

                    for prod in rule.expression.iter() {
                        let mut count = 0;

                        for symbol in prod.iter() {
                            let s_first = self.first(vec![*symbol]);

                            x_set.extend(s_first.iter().filter(IsNotEpsilon::is_not_epsilon));

                            if !s_first.contains(&"") {
                                break;
                            }
                            count += 1;
                        }
                        //if first(Y[j]) for j in 1..k contains "empty", then add it to the first(X)
                        if count == prod.len() {
                            x_set.insert(&"");
                        }
                    }
                }
            };
            let contains_epsilon = x_set.contains(&"");
            set.extend(x_set);
            if !contains_epsilon {
                break;
            }
        }
        set
    }

    pub fn get_rule(&self, name: &str) -> Option<&GrammarRule<'a, 'b>> {
        self.rules.iter().filter(|r| r.name == name).next()
    }

    pub fn get_non_terminals(&self) -> HashSet<GrammarSymbol> {
        self.rules.iter().map(|r| NonTerminal(r.name)).collect()
    }

    pub fn get_terminals(&self) -> HashSet<GrammarSymbol> {
        let mut terminals: HashSet<GrammarSymbol> = hash_set!(Terminal("$"));
        for rule in self.rules.iter() {
            for prod in rule.expression.iter() {
                for sym in prod.iter() {
                    if let Terminal(_) = sym {
                        terminals.insert(sym.clone());
                    }
                }
            }
        }
        terminals
    }
}

mod impls {
    use super::*;
    use lex::Token;
    use std::fmt::{Display, Formatter, Result};

    impl<'a> GrammarSymbol<'a> {
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
}

#[cfg(test)]
mod test {
    use super::*;

    const FILENAME: &str = "test.bnf";

    #[test]
    fn test_grammar_symbol() {
        let symbol = Terminal("");
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
                    GrammarSymbol::Terminal("")
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
        assert_eq!(grammar.first(vec![NonTerminal("A")]), hash_set!["a", ""]);
        assert_eq!(
            grammar.first(vec![NonTerminal("S")]),
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
            grammar.first(vec![NonTerminal("B"), NonTerminal("A")]),
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
        assert_eq!(grammar.first(vec![NonTerminal("E'")]), hash_set!["+", ""]);
        assert_eq!(grammar.first(vec![NonTerminal("T'")]), hash_set!["*", ""]);
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
