use ndarray::Array2;
use std::collections::HashMap;
use syn::bnf::*;

pub fn construct_table<'a>(
    grammar: &'a Grammar,
) -> (
    Array2<Option<GrammarProduction<'a>>>,
    HashMap<GrammarSymbol<'a>, usize>,
) {
    let terminals = grammar.get_terminals();
    let nonterminals = grammar.get_nonterminals();
    let mut symbol_map = HashMap::new();
    for i in 0..(terminals.len()) {
        symbol_map.insert(terminals[i].clone(), i);
    }
    for i in 0..(nonterminals.len()) {
        symbol_map.insert(nonterminals[i].clone(), i);
    }
    let mut table = Array2::from_elem((nonterminals.len(), terminals.len()), None);
    for rule in grammar.rules.iter() {
        for prod in rule.expression.iter() {
            let first_a = grammar.first(prod.clone());
            for &a in first_a.iter() {
                if a != "" {
                    let i = symbol_map.get(&GrammarSymbol::Nonterminal(rule.name)).unwrap();
                    let j = symbol_map.get(&GrammarSymbol::Terminal(a)).unwrap();
                    table[[*i, *j]] = Some(GrammarProduction(
                        GrammarSymbol::Nonterminal(rule.name),
                        prod.clone(),
                    ));
                }
            }
            if first_a.contains(&"") {
                for &b in grammar.follow(GrammarSymbol::Nonterminal(rule.name)).iter() {
                    if b != "" {
                        let i = symbol_map.get(&GrammarSymbol::Nonterminal(rule.name)).unwrap();
                        let j = symbol_map.get(&GrammarSymbol::Terminal(b)).unwrap();
                        table[[*i, *j]] = Some(GrammarProduction(
                            GrammarSymbol::Nonterminal(rule.name),
                            prod.clone(),
                        ));
                    }
                }
            }
        }
    }
    (table, symbol_map)
}
