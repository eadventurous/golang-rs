#[allow(unused)]
use ::lex::{Token, TokensExt};
use id_tree::*;
use id_tree::InsertBehavior::*;
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
    let terminals_len = terminals.len();
    let non_terminals = grammar.get_non_terminals();
    let non_terminals_len = non_terminals.len();

    let mut symbol_map = HashMap::new();

    // map terminals onto their indices
    symbol_map.extend(terminals
        .into_iter()
        .enumerate()
        .map(|(i, t)| (t, i)));

    symbol_map.extend(non_terminals
        .into_iter()
        .enumerate()
        .map(|(i, t)| (t, i)));

    let mut table = Array2::from_elem((non_terminals_len, terminals_len), None);
    for rule in grammar.rules.iter() {
        for prod in rule.expression.iter() {
            let first_a = grammar.first(prod.clone());
            for &a in first_a.iter() {
                if a != "" {
                    let i = symbol_map[&GrammarSymbol::NonTerminal(rule.name)];
                    let j = symbol_map[&GrammarSymbol::Terminal(a)];
                    table[[i, j]] = Some(GrammarProduction(
                        GrammarSymbol::NonTerminal(rule.name),
                        prod.clone(),
                    ));
                }
            }
            if first_a.contains(&"") {
                #[allow(non_snake_case)]
                let follow_A = grammar.follow(GrammarSymbol::NonTerminal(rule.name), start_symbol);
                let i = symbol_map[&GrammarSymbol::NonTerminal(rule.name)];
                if follow_A.contains(&"$") {
                    let j = symbol_map[&GrammarSymbol::Terminal("$")];
                    table[[i, j]] = Some(GrammarProduction(
                        GrammarSymbol::NonTerminal(rule.name),
                        prod.clone(),
                    ));
                }
                for &b in follow_A.iter() {
                    if b != "" {
                        let j = symbol_map[&GrammarSymbol::Terminal(b)];
                        table[[i, j]] = Some(GrammarProduction(
                            GrammarSymbol::NonTerminal(rule.name),
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
    mut tokens: Vec<String>,
) -> Result<Tree<String>, String> {
    let (table, symbol_map) = construct_table(grammar, start_symbol);

    //construct tree
    let mut tree: Tree<String> = TreeBuilder::new()
        .with_node_capacity(symbol_map.len())
        .build();

    let root_str = start_symbol.to_str();
    let root_id: NodeId = tree.insert(Node::new(root_str.clone()), AsRoot).unwrap();

    tokens.push("$".to_string());
    let mut iter = tokens.iter();
    let mut stack: Vec<(GrammarSymbol, NodeId)> = Vec::new();
    stack.push((Terminal("$"), root_id.clone()));
    stack.push((start_symbol, root_id));

    let mut i = 1;
    let mut input = iter.next().unwrap();
    while !stack.is_empty() {
        //println!("stack: {:?}, input: {}", stack, input);
        if stack.last().unwrap().0 == GrammarSymbol::Terminal(&*input) {
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
            let i = symbol_map[&stack.last().unwrap().0];
            let j = symbol_map[&GrammarSymbol::Terminal(&*input)];
            match table[[i, j]] {
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
    use lang::{brainfuck, golang};
    use super::*;

    #[test]
    fn test_table() {
        let source = &r#"<E> ::= <T> <E'>
                        <E'> ::= "+" <T> <E'> | ""
                        <T> ::= <F> <T'>
                        <T'> ::= "*" <F> <T'> | ""
                        <F> ::= "(" <E> ")" | "id" "#[..];
        let grammar = Grammar::from_str(source);
        let (table, symbol_map) = construct_table(&grammar, NonTerminal("E"));
        let i = symbol_map[&GrammarSymbol::NonTerminal("E\'")];
        let j = symbol_map[&GrammarSymbol::Terminal("+")];
        let expected = vec![Terminal("+"), NonTerminal("T"), NonTerminal("E\'")];
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
        let tokens = lexer.into_tokens(input).into_raw();
        //print_tokens(tokens.clone());
        let tokens_str = tokens.map(|t| t.describe()).collect();
        assert!(parse_tokens(&grammar, NonTerminal("E"), tokens_str).is_ok());

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
        let tokens = lexer.into_tokens(input).into_raw();
        //print_tokens(tokens.clone());
        let tokens_str = tokens.map(|t| t.describe()).collect();
        assert!(parse_tokens(&grammar, NonTerminal("Code"), tokens_str).is_ok());

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
        let tokens = lexer.into_tokens(input).into_raw();
        //sprint_tokens(tokens.clone());
        let tokens_str = tokens.map(|t| t.describe()).collect();
        assert!(parse_tokens(&grammar, NonTerminal("E"), tokens_str).is_err());
        /*println!("Pre-order:");
        for node in tree.traverse_pre_order(tree.root_node_id().unwrap()).unwrap() {
            print!("{}, ", node.data());
        }*/
    }
}
