//! Predictive parser based on BNF grammar.
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
#[allow(unused)]
use ::lex::{Token, TokensExt};
use id_tree::*;
use id_tree::InsertBehavior::*;
use ndarray::Array2;
use std::collections::HashMap;
use super::bnf::*;

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

    let mut symbol_map = hash_map! {};

    // map terminals and non-terminals onto their indices
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
            #[allow(non_snake_case)]
            let first_A = grammar.first(prod.clone());
            for &a in first_A.iter().filter(IsNotEpsilon::is_not_epsilon) {
                let i = symbol_map[&GrammarSymbol::NonTerminal(rule.name)];
                let j = symbol_map[&GrammarSymbol::Terminal(a)];
                table[[i, j]] = Some(GrammarProduction(
                    GrammarSymbol::NonTerminal(rule.name),
                    prod.clone(),
                ));
            }
            if first_A.contains(&"") {
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

                for &b in follow_A.iter().filter(IsNotEpsilon::is_not_epsilon) {
                    let j = symbol_map[&GrammarSymbol::Terminal(b)];
                    table[[i, j]] = Some(GrammarProduction(
                        GrammarSymbol::NonTerminal(rule.name),
                        prod.clone(),
                    ));
                }
            }
        }
    }
    (table, symbol_map)
}

pub fn parse_tokens<'a, 'b>(
    grammar: &'a Grammar,
    root_symbol: GrammarSymbol<'a>,
    tokens: Vec<String>,
) -> Result<Tree<String>, String> {
    let (table, symbol_map) = construct_table(grammar, root_symbol);

    //construct tree
    let mut tree: Tree<String> = TreeBuilder::new()
        .with_node_capacity(symbol_map.len())
        .build();

    let root_str = root_symbol.to_str();
    let root_id: NodeId = tree.insert(Node::new(root_str.clone()), AsRoot)
                              .map_err(|e| format!("{}", e))?;

    let mut iter = tokens.into_iter().chain(::std::iter::once("$".to_string()));
    let mut stack: Vec<(GrammarSymbol, NodeId)> = vec![
        (Terminal("$"), root_id.clone()),
        (root_symbol, root_id),
    ];

    let mut i = 1;
    let mut input = iter.next().unwrap(); // Never empty. At least `chain` provides one "$" string.

    // same as `while !stack.is_empty() { let (..) = stack.last().unwrap(); ... }`
    while let Some((last_symbol, last_node_id)) = stack.last().cloned() {
        //println!("stack: {:?}, input: {}", stack, input);
        match last_symbol {
            GrammarSymbol::Terminal(s) if s == input => {
                stack.pop()
                     .ok_or_else(|| "Empty stack!".to_string())?;
                if !stack.is_empty() {
                    input = iter.next()
                                .ok_or_else(|| "No more tokens!".to_string())?;
                    i += 1;
                }
            }
            GrammarSymbol::Terminal(s) => Err(format!(
                "Expected {:?}, got {} at token number {}",
                last_symbol,
                s,
                i
            ))?,
            _ => {
                let i = *symbol_map.get(&last_symbol)
                                   .ok_or_else(|| format!("Non-terminal {:?} not found!", last_symbol))?;
                let j = *symbol_map.get(&GrammarSymbol::Terminal(&*input))
                                   .ok_or_else(|| format!("Terminal {:?} not found!", input))?;
                let prod = table[[i, j]].as_ref()
                                        .ok_or_else(|| format!(
                                            "No grammar rule for {:?} given {} at token number {}",
                                            last_symbol,
                                            input,
                                            i
                                        ))?;
                //println!("{:?}", prod);

                stack.pop()
                     .ok_or_else(|| "Empty stack!".to_string())?;

                for &symbol in prod.1.iter().rev().filter(IsNotEpsilon::is_not_epsilon) {
                    let node_id = tree
                        .insert(
                            Node::new(symbol.to_str()),
                            UnderNode(&last_node_id),
                        )
                        .map_err(|e| format!("{}", e))?;
                    stack.push((symbol, node_id));
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

    #[allow(unused)]
    fn print_tree<T: ::std::fmt::Display>(tree: &Tree<T>) {
        fn inner<T: ::std::fmt::Display>(tree: &Tree<T>, node: &Node<T>, level: usize) {
            let indent = "  ".repeat(level);
            let tick = ['-', '+', '*'][level % 3];
            println!("{}{} {}", indent, tick, node.data());

            for child in node.children() {
                let child = tree.get(child).unwrap();
                inner(tree, child, level + 1);
            }
        }
        match tree.root_node_id().and_then(|id| tree.get(id).ok()) {
            Some(node_id) => inner(tree, node_id, 0),
            None => println!("Empty tree"),
        }
    }

    #[test]
    fn test_table() {
        let source = r#"
            <E> ::= <T> <E'>
            <E'> ::= "+" <T> <E'> | ""
            <T> ::= <F> <T'>
            <T'> ::= "*" <F> <T'> | ""
            <F> ::= "(" <E> ")" | "id"
        "#;
        let grammar = Grammar::from_str(source).unwrap();
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
        let source = r#"
            <E> ::= <T> <E'>
            <E'> ::= "Operator(Add)" <T> <E'> | ""
            <T> ::= <F> <T'>
            <T'> ::= "Operator(Mul)" <F> <T'> | ""
            <F> ::= "(" <E> ")" | "id"
        "#;
        let grammar = Grammar::from_str(source).unwrap();
        let lexer = golang::make_lexer();
        let input = "id + id * id";
        let tokens = lexer.into_tokens(input).into_raw();

        let tokens_str = tokens.map(|t| t.describe()).collect();
        assert!(parse_tokens(&grammar, NonTerminal("E"), tokens_str).is_ok());

        /*println!("Pre-order:");
        for node in tree.traverse_pre_order(tree.root_node_id().unwrap()).unwrap() {
            print!("{}, ", node.data());
        }*/
    }

    #[test]
    fn test_parser_brainf() {
        let source = r#"
            <Code> ::= <Command> <Code> | ""
            <Command> ::= "Inc" | "Dec" | "Left" | "Right" | "Input" | "Output" | "Cond" <Code> "Loop" | "Comment"
        "#;
        let grammar = Grammar::from_str(source).unwrap();
        let lexer = brainfuck::make_lexer();
        let input = ",[.-[-->++<]>+]";
        let tokens = lexer.into_tokens(input).into_raw();

        let tokens_str = tokens.map(|t| t.describe()).collect();
        let result = parse_tokens(&grammar, NonTerminal("Code"), tokens_str);
        assert!(result.is_ok());

        // let tree = result.unwrap();
        // print_tree(&tree);
    }

    #[test]
    fn test_parser_error() {
        let source = r#"
            <E> ::= <T> <E'>
            <E'> ::= "Operator(Add)" <T> <E'> | ""
            <T> ::= <F> <T'>
            <T'> ::= "Operator(Mul)" <F> <T'> | ""
            <F> ::= "(" <E> ")" | "id"
        "#;
        let grammar = Grammar::from_str(source).unwrap();
        let lexer = golang::make_lexer();
        let input = "id + + * id";
        let tokens = lexer.into_tokens(input).into_raw();

        let tokens_str = tokens.map(|t| t.describe()).collect();
        assert!(parse_tokens(&grammar, NonTerminal("E"), tokens_str).is_err());
    }
}
