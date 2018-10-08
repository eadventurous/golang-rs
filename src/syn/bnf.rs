#[derive(Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Debug, Hash)]
pub enum GrammarSymbol<'a> {
    Terminal(&'a str),
    Nonterminal(&'a str),
}

#[derive(Clone, Debug)]
pub struct GrammarProduction<'a> (pub GrammarSymbol<'a>, pub Vec<GrammarSymbol<'a>>);

pub struct GrammarRule<'a, 'b> {
    pub name: &'a str,
    pub expression: Vec<Vec<GrammarSymbol<'b>>>,
}

impl<'a, 'b> GrammarRule<'a, 'b> {
    fn from_str(s: &str) -> GrammarRule {
        //TODO: parse string
        GrammarRule {
            name: "name",
            expression: vec![],
        }
    }
}

pub struct Grammar<'a, 'b> {
    pub rules: Vec<GrammarRule<'a, 'b>>,
}

pub use self::GrammarSymbol::*;

impl<'a, 'b> Grammar<'a, 'b> {
    pub fn from_str(s: &str) -> Grammar {
        let mut rules = Vec::new();
        for _ in s.lines() {
            rules.push(GrammarRule::from_str(s));
        }
        Grammar { rules }
    }

    pub fn follow(&self, token: GrammarSymbol) -> Vec<&'b str> {
        let mut set = Vec::new();
        for rule in self.rules.iter() {
            for prod in rule.expression.iter() {
                if let Some(i) = prod.iter().position(|&s| s == token) {
                    let (_, follow_symbols) = prod.split_at(i + 1);
                    let mut has_empty = true;
                    for follow_symbol in follow_symbols.iter() {
                        let first_set = self.first(vec![*follow_symbol]);
                        for a in first_set.iter() {
                            if *a != "" {
                                set.push(*a);
                            }
                        }
                        if !first_set.contains(&"") {
                            has_empty = false;
                            break;
                        }
                    }
                    if has_empty {
                        set.append(&mut self.follow(Nonterminal(rule.name)));
                    }
                }
            }
        }
        set
    }

    pub fn first(&self, tokens: Vec<GrammarSymbol<'b>>) -> Vec<&'b str> {
        let mut set: Vec<&str> = Vec::new();
        for token in tokens.iter() {
            match *token {
                Terminal(s) => set.push(s),
                Nonterminal(_) => {
                    let rule = self.get_rule(token).unwrap();
                    for prod in rule.expression.iter() {
                        let mut count = 0;
                        for symbol in prod.iter() {
                            let s_first = self.first(vec![*symbol]);
                            for a in s_first.iter() {
                                if *a != "" {
                                    set.push(a);
                                }
                            }
                            count += 1;
                            if !s_first.contains(&"") {
                                break;
                            }
                        }
                        //if first(Y[j]) for j in 1..k contains "empty", then add it to the first(X)
                        if count == prod.len() {
                            set.push(&"");
                        }
                    }
                }
            };
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
        terminals
    }
}
