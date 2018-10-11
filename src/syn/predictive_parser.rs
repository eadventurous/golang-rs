use lex::Token;
use ndarray::Array2;
use std::collections::HashMap;
use syn::bnf::*;

fn construct_table<'a>(
    grammar: &'a Grammar,
    start_symbol: GrammarSymbol,
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
                    let i = symbol_map
                        .get(&GrammarSymbol::Nonterminal(rule.name))
                        .unwrap();
                    let j = symbol_map.get(&GrammarSymbol::Terminal(a)).unwrap();
                    table[[*i, *j]] = Some(GrammarProduction(
                        GrammarSymbol::Nonterminal(rule.name),
                        prod.clone(),
                    ));
                }
            }
            if first_a.contains(&"") {
                let follow_A = grammar.follow(GrammarSymbol::Nonterminal(rule.name), start_symbol);
                let i = symbol_map
                            .get(&GrammarSymbol::Nonterminal(rule.name))
                            .unwrap();
                if follow_A.contains(&"$") {
                    let j = symbol_map.get(&GrammarSymbol::Terminal("$")).unwrap();
                        table[[*i, *j]] = Some(GrammarProduction(
                            GrammarSymbol::Nonterminal(rule.name),
                            prod.clone(),
                        ));
                }
                for &b in follow_A.iter() {
                    if b != "" {
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

pub fn parse_tokens<'a, 'b>(
    grammar: &'a Grammar,
    start_symbol: GrammarSymbol,
    tokens: Vec<String>,
) {
    let (table, symbol_map) = construct_table(grammar, start_symbol);
    let mut tokens = tokens.clone();
    tokens.push("$".to_string());
    let mut iter = tokens.iter();
    let mut stack: Vec<GrammarSymbol> = Vec::new();
    stack.push(Terminal("$"));
    stack.push(start_symbol);
    let mut input = iter.next().unwrap();
    while !stack.is_empty() {
        println!("stack: {:?}, input: {}", stack, input);
        if *stack.last().unwrap() == GrammarSymbol::Terminal(&input) {
            stack.pop();
            if !stack.is_empty(){
                input = iter.next().unwrap();
            }
        } else if let GrammarSymbol::Terminal(_) = *stack.last().unwrap() {
            panic!("Terminal encountered but nonterminal expected.")
        } else {
            let i = symbol_map.get(stack.last().unwrap()).unwrap();
            let j = symbol_map.get(&GrammarSymbol::Terminal(&input)).unwrap();
            match table[[*i, *j]] {
                None => panic!("Empty parse table entry."),
                Some(ref prod) => {
                    println!("{:?}", prod);
                    stack.pop();
                    for symbol in prod.1.iter().rev() {
                        if let Terminal("") = symbol{
                            continue;
                        }
                        stack.push(*symbol);
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use engine;
    use lang::golang::*;
    use ::print_tokens;

    #[test]
    fn test_table() {
        let source = &r#"<E> ::= <T> <E'>
                        <E'> ::= "+" <T> <E'> | ""
                        <T> ::= <F> <T'>
                        <T'> ::= "*" <F> <T'> | ""
                        <F> ::= "(" <E> ")" | "id" "#[..];
        let grammar = Grammar::from_str(source);
        let (table, symbol_map) = construct_table(&grammar, Nonterminal("E"));
        let &i = symbol_map.get(&GrammarSymbol::Nonterminal("E\'")).unwrap();
        let &j = symbol_map.get(&GrammarSymbol::Terminal("+")).unwrap();
        let expected = vec![Terminal("+"), Nonterminal("T"), Nonterminal("E\'")];
        if let Some(ref prod) = table[[i, j]] {
            assert_eq!(prod.1, expected);
        }
    }

    #[test]
    fn test_parser() {
        let source = &r#"<E> ::= <T> <E'>
                        <E'> ::= "Operator(Add)" <T> <E'> | ""
                        <T> ::= <F> <T'>
                        <T'> ::= "Operator(Mul)" <F> <T'> | ""
                        <F> ::= "(" <E> ")" | "id" "#[..];
        let grammar = Grammar::from_str(source);
        let lexer = make_lexer();
        let input = "id + id * id";
        let tokens = engine(&lexer, input).unwrap();
        print_tokens(tokens.clone());
        let tokens_str = tokens.iter().map(|t| t.describe()).collect();
        parse_tokens(&grammar, Nonterminal("E"), tokens_str);
    }
}
