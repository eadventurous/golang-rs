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
use super::bnf::*;
use id_tree::InsertBehavior::*;
use id_tree::*;
#[allow(unused)]
use lex::{MetaResult, Token, TokensExt};
use ndarray::Array2;
use std::collections::HashMap;

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

    let mut symbol_map = hash_map!{};

    // map terminals and non-terminals onto their indices
    symbol_map.extend(terminals.into_iter().enumerate().map(|(i, t)| (t, i)));

    symbol_map.extend(non_terminals.into_iter().enumerate().map(|(i, t)| (t, i)));

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

/// Parse vector of string tokens according to given `grammar`.
/// Starts from `root_symbol` which must be one of `grammar`'s non-terminals.
///
/// # Returns
///
/// `Ok(`[`Tree`]`)` whose root element is `root_symbol` or `Err()` with string description.
///
/// [`Tree`]: https://docs.rs/id_tree/1.3.0/id_tree/struct.Tree.html
pub fn parse_tokens<'a, 'b, I, T>(
    grammar: &'a Grammar,
    root_symbol: GrammarSymbol<'a>,
    tokens: I,
) -> Result<Tree<String>, String>
where
    I: Iterator<Item = MetaResult<'a, T>>,
    T: Token<'a>,
{
    let (table, symbol_map) = construct_table(grammar, root_symbol);

    //construct tree
    let mut tree: Tree<String> = TreeBuilder::new()
        .with_node_capacity(symbol_map.len())
        .build();

    let root_str = root_symbol.to_str();
    let root_id: NodeId = tree
        .insert(Node::new(root_str.clone()), AsRoot)
        .map_err(|e| format!("{}", e))?;

    let tokens_str = tokens
        .map(|t| {
            let token = t.unwrap().token;
            (token.descriptor(), Some(token))
        }).collect::<Vec<_>>();
    let mut iter = tokens_str.into_iter().chain(::std::iter::once(("$", None)));

    let mut stack: Vec<(GrammarSymbol, NodeId)> =
        vec![(Terminal("$"), root_id.clone()), (root_symbol, root_id)];

    let mut i = 1;
    let mut input = iter.next().unwrap(); // Never empty. At least `chain` provides one "$" string.

    // same as `while !stack.is_empty() { let (..) = stack.last().unwrap(); ... }`
    while let Some((last_symbol, last_node_id)) = stack.last().cloned() {
        //println!("stack: {:?}, input: {}", stack, input);
        match last_symbol {
            GrammarSymbol::Terminal(s) if s == input.0 => {
                if let Some(token) = &input.1 {
                    tree.get_mut(&last_node_id)
                        .unwrap()
                        .replace_data(token.describe());
                }

                stack.pop().ok_or_else(|| "Empty stack!".to_string())?;
                if !stack.is_empty() {
                    input = iter.next().ok_or_else(|| "No more tokens!".to_string())?;
                    i += 1;
                }
            }
            GrammarSymbol::Terminal(s) => Err(format!(
                "Expected {:?}, got {} at token number {}",
                last_symbol, s, i
            ))?,
            _ => {
                let i = *symbol_map
                    .get(&last_symbol)
                    .ok_or_else(|| format!("Non-terminal {:?} not found!", last_symbol))?;
                let j = *symbol_map
                    .get(&GrammarSymbol::Terminal(input.0))
                    .ok_or_else(|| format!("Terminal {:?} not found!", input))?;
                let prod = table[[i, j]].as_ref().ok_or_else(|| {
                    format!(
                        "No grammar rule for {:?} given {} at token number {}",
                        last_symbol, input.0, i
                    )
                })?;
                //println!("{:?}", prod);

                stack.pop().ok_or_else(|| "Empty stack!".to_string())?;

                let symbols_and_ids: Vec<(GrammarSymbol, NodeId)> = prod
                    .1
                    .iter()
                    .filter(IsNotEpsilon::is_not_epsilon)
                    .map(|symbol| {
                        tree.insert(Node::new(symbol.to_str()), UnderNode(&last_node_id))
                            .map(|id| (*symbol, id))
                            .map_err(|e| format!("{}", e))
                    }).collect::<Result<_, String>>()?;

                stack.extend(symbols_and_ids.into_iter().rev());
            }
        }
    }
    Ok(tree)
}

#[cfg(test)]
mod test {
    use super::*;
    use lang::{brainfuck, golang};
    use tree_util::*;

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
        let i = symbol_map[&GrammarSymbol::NonTerminal("E'")];
        let j = symbol_map[&GrammarSymbol::Terminal("+")];
        let expected = vec![Terminal("+"), NonTerminal("T"), NonTerminal("E'")];
        if let Some(ref prod) = table[[i, j]] {
            assert_eq!(prod.1, expected);
        }
    }

    #[test]
    fn test_parser_expr() {
        let source = r#"
            <E> ::= <T> <E'>
            <E'> ::= "Add" <T> <E'> | ""
            <T> ::= <F> <T'>
            <T'> ::= "Mul" <F> <T'> | ""
            <F> ::= "(" <E> ")" | "Ident"
        "#;
        let grammar = Grammar::from_str(source).unwrap();
        let lexer = golang::make_lexer();
        let input = "one + two * three";
        let tokens = lexer.into_tokens(input);
        let tree = parse_tokens(&grammar, NonTerminal("E"), tokens).unwrap();

        let expected = tree!{
          "E" => {
            "T" => {
              "F" => {
                "one"},
              "T'"},
            "E'" => {
              "Operator(Add)",
              "T" => {
                "F" => {
                  "two"},
                "T'" => {
                  "Operator(Mul)"},
                  "F" => {
                    "tree"},
                  "T'"},
              "E'"}}
        };

        // println!("{}", TreeFmt(&tree));

        assert!(expected.eq(&tree));
    }

    #[test]
    fn test_parser_brainf() {
        let source = r#"
            <Code> ::= <Command> <Code> | ""
            <Command> ::= "Inc" | "Dec" | "Left" | "Right" | "Input" | "Output" | "Cond" <Code> "Loop" | "Comment"
        "#;
        let grammar = Grammar::from_str(source).unwrap();
        // println!("{:#?}", grammar);
        let input = ",[.-[-->++<]>+]";
        let tokens = brainfuck::make_lexer().into_tokens(input);
        let tree = parse_tokens(&grammar, NonTerminal("Code"), tokens).unwrap();

        let code_children: Vec<_> = tree
            .children(tree.root_node_id().unwrap())
            .unwrap()
            .map(Node::data)
            .collect();
        assert_eq!(code_children, vec!["Command", "Code"]);

        let mut code_children_ids = tree.children_ids(tree.root_node_id().unwrap()).unwrap();
        let mut command_children_ids = tree
            .children_ids(&code_children_ids.next().unwrap())
            .unwrap();
        let first_command_node = tree.get(command_children_ids.next().unwrap()).unwrap();

        assert_eq!("Input", first_command_node.data());

        // println!("{}", TreeFmt(&tree));
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
        let tokens = lexer.into_tokens(input);
        assert!(parse_tokens(&grammar, NonTerminal("E"), tokens).is_err());
    }
}
