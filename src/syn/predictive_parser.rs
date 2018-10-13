use id_tree::InsertBehavior::*;
use id_tree::*;
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
    start_symbol: GrammarSymbol<'a>,
    tokens: Vec<String>,
) -> Result<Tree<String>, String> {
    let (table, symbol_map) = construct_table(grammar, start_symbol);

    //construct tree
    let mut tree: Tree<String> = TreeBuilder::new()
        .with_node_capacity(symbol_map.len())
        .build();

    let root_str = start_symbol.to_str();
    let root_id: NodeId = tree.insert(Node::new(root_str.clone()), AsRoot).unwrap();

    let mut tokens = tokens.clone();
    tokens.push("$".to_string());
    let mut iter = tokens.iter();
    let mut stack: Vec<(GrammarSymbol, NodeId)> = Vec::new();
    stack.push((Terminal("$"), root_id.clone()));
    stack.push((start_symbol, root_id));
    let mut i = 1;
    let mut input = iter.next().unwrap();
    while !stack.is_empty() {
        //println!("stack: {:?}, input: {}", stack, input);
        if stack.last().unwrap().0 == GrammarSymbol::Terminal(&input) {
            stack.pop();
            if !stack.is_empty() {
                input = iter.next().unwrap();
                i += 1;
            }
        } else if let GrammarSymbol::Terminal(s) = stack.last().unwrap().0 {
            let error_msg = format!(
                "Expected {:?}, got {} at token number {}",
                stack.last().unwrap().0,
                s,
                i
            );
            //println!("{}", error_msg);
            return Err(error_msg);
        } else {
            let i = symbol_map.get(&stack.last().unwrap().0).unwrap();
            let j = symbol_map.get(&GrammarSymbol::Terminal(&input)).unwrap();
            match table[[*i, *j]] {
                None => {
                    let error_msg = format!(
                        "No grammar rule for {:?} given {} at token number {}",
                        stack.last().unwrap().0,
                        input,
                        i
                    );
                    //println!("{}", error_msg);
                    return Err(error_msg);
                }
                Some(ref prod) => {
                    //println!("{:?}", prod);
                    stack.pop();
                    for symbol in prod.1.iter().rev() {
                        if let Terminal("") = symbol {
                            continue;
                        }
                        let node_id: NodeId = tree
                            .insert(
                                Node::new(symbol.to_str()),
                                UnderNode(&stack.last().unwrap().1),
                            ).unwrap();
                        stack.push((*symbol, node_id));
                    }
                }
            }
        }
    }
    Ok(tree)
}

#[cfg(test)]
mod test {
    use super::*;
    use engine;
    use lang::{brainfuck, golang};
    use print_tokens;

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
    fn test_parser_expr() {
        let source = &r#"<E> ::= <T> <E'>
                        <E'> ::= "Operator(Add)" <T> <E'> | ""
                        <T> ::= <F> <T'>
                        <T'> ::= "Operator(Mul)" <F> <T'> | ""
                        <F> ::= "(" <E> ")" | "id" "#[..];
        let grammar = Grammar::from_str(source);
        let lexer = golang::make_lexer();
        let input = "id + id * id";
        let tokens = engine(&lexer, input).unwrap();
        //print_tokens(tokens.clone());
        let tokens_str = tokens.iter().map(|t| t.describe()).collect();
        assert!(parse_tokens(&grammar, Nonterminal("E"), tokens_str).is_ok());

        /*println!("Pre-order:");
        for node in tree.traverse_pre_order(tree.root_node_id().unwrap()).unwrap() {
            print!("{}, ", node.data());
        }*/
    }

    #[test]
    fn test_parser_brainf() {
        let source = &r#"<Code> ::= <Command> <Code> | ""
                        <Command> ::= "Inc" | "Dec" | "Left" | "Right" | "Input" | "Output" | "Cond" <Code> "Loop" | "Comment" "#[..];
        let grammar = Grammar::from_str(source);
        let lexer = brainfuck::make_lexer();
        let input = ",[.-[-->++<]>+]";
        let tokens = engine(&lexer, input).unwrap();
        //print_tokens(tokens.clone());
        let tokens_str = tokens.iter().map(|t| t.describe()).collect();
        assert!(parse_tokens(&grammar, Nonterminal("Code"), tokens_str).is_ok());

        /*println!("Pre-order:");
        for node in tree.traverse_pre_order(tree.root_node_id().unwrap()).unwrap() {
            print!("{}, ", node.data());
        }*/
    }

    #[test]
    fn test_parser_error() {
        let source = &r#"<E> ::= <T> <E'>
                        <E'> ::= "Operator(Add)" <T> <E'> | ""
                        <T> ::= <F> <T'>
                        <T'> ::= "Operator(Mul)" <F> <T'> | ""
                        <F> ::= "(" <E> ")" | "id" "#[..];
        let grammar = Grammar::from_str(source);
        let lexer = golang::make_lexer();
        let input = "id + + * id";
        let tokens = engine(&lexer, input).unwrap();
        //sprint_tokens(tokens.clone());
        let tokens_str = tokens.iter().map(|t| t.describe()).collect();
        assert!(parse_tokens(&grammar, Nonterminal("E"), tokens_str).is_err());
        /*println!("Pre-order:");
        for node in tree.traverse_pre_order(tree.root_node_id().unwrap()).unwrap() {
            print!("{}, ", node.data());
        }*/
    }
}
