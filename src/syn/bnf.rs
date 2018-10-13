use engine;
use lex::{Lexer, LexerBuilder, Token};

#[derive(Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Debug, Hash)]
pub enum GrammarSymbol<'a> {
    Terminal(&'a str),
    Nonterminal(&'a str),
}

impl<'a> GrammarSymbol<'a> {
    pub fn to_str(&self) -> String{
        let s = match self.clone() {
            Terminal(s) => s,
            Nonterminal(s) => s,
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
    Nonterminal(&'a str),
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
            BnfToken::Nonterminal(c.get(0).unwrap().as_str())
        }).add("\".*?\"", |c| {
            BnfToken::Terminal(c.get(0).unwrap().as_str())
        }).build()
}

impl<'a> Token<'a> for BnfToken<'a> {
    fn describe(&self) -> String {
        format!("{:?}", self)
    }
}

impl<'a, 'b> GrammarRule<'a, 'b> {
    fn from_str(s: &str) -> GrammarRule {
        let lexer = make_lexer();
        println!("{}", s);
        let tokens = engine(&lexer, s).unwrap();
        let mut tokens_iter = tokens.iter();
        let name = match tokens_iter.next().unwrap() {
            BnfToken::Nonterminal(s) => &s[1..(s.len() - 1)],
            _ => panic!("Nonterminal expected at the start of the rule."),
        };
        match tokens_iter.next().unwrap() {
            BnfToken::Operator(BnfOperator::Equals) => {}
            _ => panic!("Equals sign expected at after the first nonterminal."),
        };
        let mut expression: Vec<Vec<GrammarSymbol>> = Vec::new();
        let mut prod: Vec<GrammarSymbol> = Vec::new();
        for token in tokens_iter {
            println!("{:?}", token);
            match token {
                BnfToken::Nonterminal(s) => prod.push(Nonterminal(&s[1..(s.len() - 1)])),
                BnfToken::Terminal(s) => prod.push(Terminal(&s[1..(s.len() - 1)])),
                BnfToken::Operator(BnfOperator::Alt) => {
                    expression.push(prod);
                    prod = Vec::new();
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

pub use self::GrammarSymbol::*;

impl<'a, 'b> Grammar<'a, 'b> {
    pub fn from_str(s: &str) -> Grammar {
        let mut rules = Vec::new();
        for line in s.lines() {
            rules.push(GrammarRule::from_str(line));
        }
        Grammar { rules }
    }

    pub fn follow(&self, token: GrammarSymbol, start_symbol: GrammarSymbol) -> Vec<&'b str> {
        let mut set: Vec<&str> = Vec::new();
        if token == start_symbol {
            set.push("$");
        }
        for rule in self.rules.iter() {
            for prod in rule.expression.iter() {
                if let Some(i) = prod.iter().position(|&s| s == token) {
                    let (_, follow_symbols) = prod.split_at(i + 1);
                    let mut has_empty = false;
                    if !follow_symbols.is_empty() {
                        let first_beta = self.first(follow_symbols.to_vec());
                        for e in first_beta.iter() {
                            if e != &"" && !set.contains(e) {
                                set.push(e);
                            }
                        }
                        if first_beta.contains(&"") {
                            has_empty = true;
                        }
                    } else {
                        has_empty = true;
                    }
                    if has_empty && (Nonterminal(rule.name) != token) {
                        let follow_a = self.follow(Nonterminal(rule.name), start_symbol);
                        for e in follow_a.iter() {
                            if !set.contains(e) {
                                set.push(e);
                            }
                        }
                    }
                }
            }
        }
        set
    }

    pub fn first(&self, tokens: Vec<GrammarSymbol<'b>>) -> Vec<&'b str> {
        let mut set: Vec<&str> = Vec::new();
        for token in tokens.iter() {
            let mut x_set: Vec<&str> = Vec::new();
            match *token {
                Terminal(s) => x_set.push(s),
                Nonterminal(_) => {
                    let rule = self.get_rule(token).unwrap();
                    for prod in rule.expression.iter() {
                        let mut count = 0;
                        for symbol in prod.iter() {
                            let s_first = self.first(vec![*symbol]);
                            for a in s_first.iter() {
                                if *a != "" && !x_set.contains(a) {
                                    x_set.push(a);
                                }
                            }
                            if !s_first.contains(&"") {
                                break;
                            }
                            count += 1;
                        }
                        //if first(Y[j]) for j in 1..k contains "empty", then add it to the first(X)
                        if count == prod.len() {
                            x_set.push(&"");
                        }
                    }
                }
            };
            let contains_empty = x_set.contains(&"");
            for e in x_set.iter() {
                if !set.contains(e) {
                    set.push(e);
                }
            }
            if !contains_empty {
                break;
            }
        }
        set
    }

    pub fn get_rule(&self, token: &GrammarSymbol) -> Option<&GrammarRule<'a, 'b>> {
        match *token {
            Nonterminal(s) => self.rules.iter().filter(|r| r.name == s).next(),
            Terminal(_) => None,
        }
    }

    pub fn get_nonterminals(&self) -> Vec<GrammarSymbol> {
        self.rules.iter().map(|r| Nonterminal(r.name)).collect()
    }

    pub fn get_terminals(&self) -> Vec<&GrammarSymbol> {
        let mut terminals: Vec<&GrammarSymbol> = Vec::new();
        for rule in self.rules.iter() {
            for prod in rule.expression.iter() {
                for sym in prod.iter() {
                    if let Terminal(_) = sym {
                        if !terminals.contains(&sym) {
                            terminals.push(sym)
                        }
                    }
                }
            }
        }
        terminals.push(&Terminal("$"));
        terminals
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use engine;

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
                    GrammarSymbol::Nonterminal("roman-numeral"),
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
        assert_eq!(grammar.first(vec![Nonterminal("A")]), vec!["a", ""]);
        assert_eq!(
            grammar.first(vec![Nonterminal("S")]),
            vec!["c", "d", "a", ""]
        );
    }

    #[test]
    fn test_first_set_multiple() {
        let source = &r#"<S> ::= "c"<A>"d" | <B><A>
                        <A> ::= "a""b" | "a" | ""
                        <B> ::= "" | "d" "#[..];
        let grammar = Grammar::from_str(source);
        assert_eq!(
            grammar.first(vec![Nonterminal("B"), Nonterminal("A")]),
            vec!["", "d", "a"]
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
        assert_eq!(grammar.first(vec![Nonterminal("E'")]), vec!["+", ""]);
        assert_eq!(grammar.first(vec![Nonterminal("T'")]), vec!["*", ""]);
    }

    #[test]
    fn test_follow_set() {
        let source = &r#"<E> ::= <T> <E'>
                        <E'> ::= "+" <T> <E'> | ""
                        <T> ::= <F> <T'>
                        <T'> ::= "*" <F> <T'> | ""
                        <F> ::= "(" <E> ")" | "id" "#[..];
        let grammar = Grammar::from_str(source);
        assert_eq!(grammar.follow(Nonterminal("E"), Nonterminal("E")), vec!["$", ")"]);
        assert_eq!(grammar.follow(Nonterminal("T"), Nonterminal("E")), vec!["+", "$",")"]);
    }
}
