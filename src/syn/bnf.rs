use ::lex::{Lexer, LexerBuilder, Token, TokensExt};
pub use self::GrammarSymbol::*;
use std::collections::hash_set::HashSet;
#[allow(unused)]
use std::iter::FromIterator;

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

#[derive(Clone, Debug)]
pub struct GrammarProduction<'a>(pub GrammarSymbol<'a>, pub Vec<GrammarSymbol<'a>>);

pub struct GrammarRule<'a, 'b> {
    pub name: &'a str,
    pub expression: Vec<Vec<GrammarSymbol<'b>>>,
}

#[derive(Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Debug)]
pub enum BnfToken<'a> {
    Terminal(&'a str),
    NonTerminal(&'a str),
    Operator(BnfOperator),
}

#[derive(Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Debug)]
pub enum BnfOperator {
    // "::="
    Equals,
    //Alternative "|"
    Alt,
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

fn make_lexer<'a>() -> Lexer<'a, BnfToken<'a>> {
    let constant = |x| move |_| x;
    LexerBuilder::new()
        .skip_whitespaces(whitespace_filter)
        .add(r"::=", constant(BnfToken::Operator(BnfOperator::Equals)))
        .add(r"\|", constant(BnfToken::Operator(BnfOperator::Alt)))
        .add(r"<.+?>", |c| {
            BnfToken::NonTerminal(c.get(0).unwrap().as_str())
        })
        .add("\".*?\"", |c| {
            BnfToken::Terminal(c.get(0).unwrap().as_str())
        })
        .build()
}

impl<'a> Token<'a> for BnfToken<'a> {}

impl<'a, 'b> GrammarRule<'a, 'b> {
    fn from_str(s: &str) -> GrammarRule {
        let lexer = make_lexer();
        let mut tokens = lexer.into_tokens(s).into_raw();
        let name = match tokens.next().unwrap() {
            BnfToken::NonTerminal(s) => &s[1..(s.len() - 1)],
            _ => panic!("NonTerminal expected at the start of the rule."),
        };
        match tokens.next().unwrap() {
            BnfToken::Operator(BnfOperator::Equals) => {}
            _ => panic!("Equals sign expected after the first nonterminal."),
        };
        let mut expression: Vec<Vec<GrammarSymbol>> = vec![];
        let mut prod: Vec<GrammarSymbol> = vec![];
        for token in tokens {
            //println!("{:?}", token);
            match token {
                BnfToken::NonTerminal(s) => prod.push(NonTerminal(&s[1..(s.len() - 1)])),
                BnfToken::Terminal(s) => prod.push(Terminal(&s[1..(s.len() - 1)])),
                BnfToken::Operator(BnfOperator::Alt) => {
                    expression.push(prod);
                    prod = vec![];
                }
                _ => panic!("Unexpected token in the expression part."),
            }
        }
        if !prod.is_empty() {
            expression.push(prod);
        }
        GrammarRule { name, expression }
    }
}

pub struct Grammar<'a, 'b> {
    pub rules: Vec<GrammarRule<'a, 'b>>,
}

impl<'a, 'b> Grammar<'a, 'b> {
    pub fn from_str(s: &str) -> Grammar {
        let mut rules = vec![];
        for line in s.lines() {
            rules.push(GrammarRule::from_str(line));
        }
        Grammar { rules }
    }

    pub fn follow(&self, token: GrammarSymbol, start_symbol: GrammarSymbol) -> HashSet<&'b str> {
        let mut set: HashSet<&str> = HashSet::new();
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
                        for e in first_beta.iter().filter(|s| !s.is_empty()) {
                            set.insert(e);
                        }
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
        let mut set: HashSet<&str> = HashSet::new();
        for token in tokens {
            let mut x_set: HashSet<&str> = HashSet::new();
            match token {
                Terminal(s) => { x_set.insert(s); }
                NonTerminal(_) => {
                    let rule = self.get_rule(&token).unwrap();
                    for prod in rule.expression.iter() {
                        let mut count = 0;
                        for symbol in prod.iter() {
                            let s_first = self.first(vec![*symbol]);
                            for a in s_first.iter() {
                                if *a != "" {
                                    x_set.insert(a);
                                }
                            }
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
            let contains_empty = x_set.contains(&"");
            set.extend(x_set);
            if !contains_empty {
                break;
            }
        }
        set
    }

    pub fn get_rule(&self, token: &GrammarSymbol) -> Option<&GrammarRule<'a, 'b>> {
        match *token {
            NonTerminal(s) => self.rules.iter().filter(|r| r.name == s).next(),
            Terminal(_) => None,
        }
    }

    pub fn get_non_terminals(&self) -> HashSet<GrammarSymbol> {
        self.rules.iter().map(|r| NonTerminal(r.name)).collect()
    }

    pub fn get_terminals(&self) -> HashSet<GrammarSymbol> {
        let mut terminals: HashSet<GrammarSymbol> = hash_set!();
        for rule in self.rules.iter() {
            for prod in rule.expression.iter() {
                for sym in prod.iter() {
                    if let Terminal(_) = sym {
                        terminals.insert(sym.clone());
                    }
                }
            }
        }
        terminals.insert(Terminal("$"));
        terminals
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_bnf_parsing_rule_name() {
        let source = &r#"<opt-suffix-part> ::= "Sr." | "Jr." | <roman-numeral> | """#[..];
        let rule = GrammarRule::from_str(source);
        assert_eq!(rule.name, "opt-suffix-part");
    }

    #[test]
    fn test_bnf_parsing_expr() {
        let source = &r#"<opt-suffix-part> ::= "Sr." | "Jr." <roman-numeral> """#[..];
        let rule = GrammarRule::from_str(source);
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
        let source = &r#"<S> ::= "c"<A>"d" | <B><A>
                        <A> ::= "a""b" | "a" | ""
                        <B> ::= "" | "d" "#[..];
        let grammar = Grammar::from_str(source);
        assert_eq!(grammar.first(vec![NonTerminal("A")]), hash_set!["a", ""]);
        assert_eq!(
            grammar.first(vec![NonTerminal("S")]),
            hash_set!["c", "d", "a", ""]
        );
    }

    #[test]
    fn test_first_set_multiple() {
        let source = &r#"<S> ::= "c"<A>"d" | <B><A>
                        <A> ::= "a""b" | "a" | ""
                        <B> ::= "" | "d" "#[..];
        let grammar = Grammar::from_str(source);
        assert_eq!(
            grammar.first(vec![NonTerminal("B"), NonTerminal("A")]),
            hash_set!["", "d", "a"]
        );
    }

    #[test]
    fn test_first_set_recursive() {
        let source = &r#"<E> ::= <T> <E'>
                        <E'> ::= "+" <T> <E'> | ""
                        <T> ::= <F> <T'>
                        <T'> ::= "*" <F> <T'> | ""
                        <F> ::= "(" <E> ")" | "id" "#[..];
        let grammar = Grammar::from_str(source);
        assert_eq!(grammar.first(vec![NonTerminal("E'")]), hash_set!["+", ""]);
        assert_eq!(grammar.first(vec![NonTerminal("T'")]), hash_set!["*", ""]);
    }

    #[test]
    fn test_follow_set() {
        let source = &r#"<E> ::= <T> <E'>
                        <E'> ::= "+" <T> <E'> | ""
                        <T> ::= <F> <T'>
                        <T'> ::= "*" <F> <T'> | ""
                        <F> ::= "(" <E> ")" | "id" "#[..];
        let grammar = Grammar::from_str(source);
        assert_eq!(grammar.follow(NonTerminal("E"), NonTerminal("E")), hash_set!["$", ")"]);
        assert_eq!(grammar.follow(NonTerminal("T"), NonTerminal("E")), hash_set!["+", "$", ")"]);
    }
}
