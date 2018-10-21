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
use lex::{ErrorBytes, MetaIter, SimpleErrorBytes, Token, TokenMeta};
use ndarray::Array2;
use std::collections::HashMap;

/// Parsing table: array of productions and its accompanying symbol map.
pub struct Table<'a> {
    table: Array2<Option<GrammarProduction<'a>>>,
    /// Symbol map for both terminals and non-terminals
    /// maps symbols onto their indices in `table` array.
    symbol_map: HashMap<GrammarSymbol<'a>, usize>,
}

#[derive(Clone, Debug)]
pub enum Error<'a> {
    FirstSetConflict {
        rule: GrammarSymbol<'a>,
        terminal: GrammarSymbol<'a>,
        conflict: Vec<GrammarProduction<'a>>,
    },
}

impl<'a> Table<'a> {
    /// Construct LL(1) table parser from given grammar.
    pub fn ll1(grammar: &'a Grammar, start_symbol: &'a str) -> Result<Self, Error<'a>> {
        #![allow(non_snake_case)]

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
            let rule_symbol = rule.symbol();
            // Index of non-terminal in table
            let i = symbol_map[&rule_symbol];

            for prod in rule.expression.iter() {
                let first_A = grammar.first(prod.clone());
                for &a in first_A.iter().filter(IsNotEpsilon::is_not_epsilon) {
                    // Index of terminal in table
                    let j = symbol_map[&Terminal(a)];

                    // Part of table construction is error checking for first/follow set conflicts.
                    if let Some(GrammarProduction(ref other)) = table[[i, j]] {
                        return Err(Error::FirstSetConflict {
                            rule: rule_symbol,
                            terminal: Terminal(a),
                            conflict: vec![
                                GrammarProduction(prod.clone()),
                                GrammarProduction(other.clone()),
                            ],
                        });
                    }
                    table[[i, j]] = Some(GrammarProduction(prod.clone()));
                }
                if first_A.contains(&"") {
                    let follow_A = grammar.follow(rule_symbol, NonTerminal(start_symbol));

                    if follow_A.contains(&"$") {
                        let j = symbol_map[&Terminal("$")];
                        if let Some(GrammarProduction(ref _other)) = table[[i, j]] {
                            // TODO
                            panic!("FOLLOW $ CONFLICT");
                        }
                        table[[i, j]] = Some(GrammarProduction(prod.clone()));
                    }

                    for &b in follow_A.iter().filter(IsNotEpsilon::is_not_epsilon) {
                        let j = symbol_map[&Terminal(b)];
                        if let Some(GrammarProduction(ref other)) = table[[i, j]] {
                            if prod != other {
                                // TODO
                                // println!("RULE {}", rule_symbol.to_str());
                                // println!("PROD {:?}", prod);
                                // println!("PROD {:?}", other);
                                panic!("FOLLOW A CONFLICT");
                            }
                        }
                        table[[i, j]] = Some(GrammarProduction(prod.clone()));
                    }
                }
            }
        }
        Ok(Table { table, symbol_map })
    }
}

pub fn parse_tokens_with_meta<'a, 'b, I, T>(
    grammar: &Grammar,
    root_symbol: &str,
    tokens: I,
    source: &'b str,
    filename: String,
) -> Result<Tree<String>, ErrorBytes<'b>>
where
    I: MetaIter<'a, T>,
    T: Token<'a>,
{
    parse_tokens(grammar, root_symbol, tokens)
        .map_err(|simple| ErrorBytes::from(simple).source(source).filename(filename))
}

/// Parse vector of string tokens according to given `grammar`.
/// Starts from `root_symbol` which must be one of `grammar`'s non-terminals.
///
/// # Returns
///
/// `Ok(`[`Tree`]`)` whose root element is `root_symbol` or `Err()` with string description.
///
/// [`Tree`]: https://docs.rs/id_tree/1.3.0/id_tree/struct.Tree.html
pub fn parse_tokens<'a, I, T>(
    grammar: &Grammar,
    root_symbol: &str,
    tokens: I,
) -> Result<Tree<String>, SimpleErrorBytes>
where
    I: MetaIter<'a, T>,
    T: Token<'a>,
{
    // Bottom of the stack is marked with this special descriptor.
    const BOTTOM: &str = "$";

    let t = Table::ll1(grammar, root_symbol).map_err(|e| format!("{}", e))?;

    // Construct a tree with node capacity equals to fourth as much as the
    // upper bound of tokens iterator. This is because usually grammars trees
    // have large amount of non-terminals comparing to number of terminals
    // which they contain as leafs.
    let capacity = 4 * tokens.size_hint().1.unwrap_or_default();
    let mut tree: Tree<String> = TreeBuilder::new().with_node_capacity(capacity).build();

    // FIXME: root may be a terminal.
    // TODO: change function signature.
    let root_symbol = NonTerminal(root_symbol);
    let root_id: NodeId = tree
        .insert(Node::new(root_symbol.to_str()), AsRoot)
        // Normally, this should never fail; but just to be on the safe side.
        .map_err(|e| format!("{}", e))?;

    // Iterator goes over input tokens, extracts their descriptors and appends special
    // terminal "$" at the end.
    // Iterator<Item=Result<(descriptor, Option<Meta>), ErrorBytes>>
    let mut iter = tokens
        .map(|result| result.map(|meta| (meta.token.descriptor(), Some(meta))))
        .chain(::std::iter::once(Ok((BOTTOM, None))));

    // Stack keeps track of pending symbols and corresponding node ids in the tree.
    // It is initialized with special terminal "$" and root symbol. Bottom terminal
    // is paired with root node id, which
    let mut stack: Vec<(GrammarSymbol, NodeId)> =
        vec![(Terminal(BOTTOM), root_id.clone()), (root_symbol, root_id)];

    // Never empty. At least `chain` provides one terminal "$".
    // let input: (descriptor, Option<MetaResult>);
    let mut input: (&str, Option<_>) = iter.next().unwrap()?;

    // This macro helper triggers an error with supplied formatting and arguments,
    // and also adds a bit of context from current input. Basically, it adds span
    // of current input, and provides current symbol as keyword argument to the
    // description's format arguments.
    //
    // It couldn't been done with `?` operator because Err value can not be
    // constructed solely from description.
    // It couldn't been done with closure either because compiler would recognise
    // it as `move` semantics for `input`, even though it would have been executed
    // only right before the return.
    //
    // Relevant link to the playground:
    // https://play.rust-lang.org/?version=stable&mode=debug&edition=2015&gist=d6bb86529997d4e41e390def3540c0a0
    macro_rules! err {
        ( $fmt:expr, $( $arg:expr, )* ) => {{
            let (span, symbol) = input.1
                .map(|meta| (meta.span, Some(meta.token)))
                .unwrap_or_default();
            let symbol = match symbol {
                Some(token) => format!("{}", token.describe()),
                None => "None".into()
            };
            return Err(
                SimpleErrorBytes::default()
                    .span(span)
                    .description(format!(
                        concat!($fmt, "{symbol:.0}"),
                        $( $arg, )*
                        symbol=symbol)));
        }};
        // Trailing comma fix.
        ( $fmt:expr, $( $arg:expr ),* ) => {{ err!( $fmt, $( $arg, )* ) }};
    }

    // Analog to early-return `?` operator for `Option`s to return error with
    // context and custom message.
    macro_rules! try_some {
        // Special case for empty arguments list.
        ( $expr:expr, $fmt:expr ) => { try_some!( $expr, $fmt, ) };
        ( $expr:expr, $fmt:expr, $( $arg:expr ),* ) => {
            match $expr {
                Some(x) => x,
                None => err!( $fmt, $( $arg ),* ),
            }
        };
    }

    // Loop until stack is empty.
    // let last_symbol: GrammarSymbol;
    // let last_node_id: NodeId;
    while let Some((last_symbol, last_node_id)) = stack.last().cloned() {
        let descriptor = input.0;
        match last_symbol {
            Terminal(s) if s == descriptor => {
                // Eventually, all grammar terminals inside the tree
                // will be replaced by corresponding tokens' descriptions.
                // Non-terminals will remain.
                // FIXME: Proposal to build tree out of special enum, not expensive `String`s
                if let (_, Some(TokenMeta { ref token, .. })) = input {
                    tree.get_mut(&last_node_id)
                        .unwrap()
                        .replace_data(token.describe());
                } else {
                    // Absence of token could mean only one reasonable thing:
                    // this is the end, and descriptor is special value "$".
                    assert_eq!(descriptor, BOTTOM);
                }

                // Done with this symbol, move on to the next.
                // Stack MUST NOT be empty at this point, because
                // empty stack is the exit condition for this loop.
                try_some!(stack.pop(), "Empty stack!");
                // If it wasn't the last expected symbol on the stack,
                // then there MUST be more inputs.
                if !stack.is_empty() {
                    input = try_some!(iter.next(), "Unexpected EOF!")?;
                }
            }
            // Not that terminal which was expected.
            // For example, for root symbol `<X> ::= "a" "b" "c"` stack would
            // look like `["$", "a", "b", "c"]` (with the first element on the
            // left); so at this point `last_symbol` is `Terminal("c")` and
            // current `input` is expected to be `Some` token with descriptor "c".
            Terminal(..) => err!(
                "Expected terminal {}, got {symbol}.",
                last_symbol.token().describe(),
            ),
            // Replace non-terminal with its production.
            NonTerminal(..) => {
                // Index of stack's current symbol in the table.
                // This must only fail if grammar is invalid.
                let i = *try_some!(
                    t.symbol_map.get(&last_symbol),
                    "Unexpected non-terminal {}.",
                    last_symbol.token().describe()
                );
                // Index of input descriptor in the table.
                // This must only fail if grammar is invalid.
                let j = *try_some!(
                    t.symbol_map.get(&Terminal(descriptor)),
                    "Unexpected terminal {}.",
                    Terminal(descriptor).token().describe()
                );
                // Lookup production
                // This may fail if input stream is not valid for given grammar.
                let prod: &GrammarProduction = try_some!(
                    t.table[[i, j]].as_ref(),
                    "Unexpected input {symbol} for grammar rule {}.",
                    last_symbol.token().describe()
                );

                // Remove old non-terminal and insert new symbols in its place.
                try_some!(stack.pop(), "Empty stack!");

                // For every non-epsilon symbol, insert its descriptor under last node.
                let symbols_and_ids: Vec<(GrammarSymbol, NodeId)> = prod
                    .iter()
                    // Don't ever put epsilon onto grammar stack:
                    // it is pointless and it won't match anything.
                    .filter(IsNotEpsilon::is_not_epsilon)
                    .map(|symbol| {
                        let as_str = symbol.to_str();
                        tree.insert(Node::new(as_str), UnderNode(&last_node_id))
                            // Normally, this should never fail; but just to be on the safe side.
                            .map_err(|e| format!("{}", e))
                            // Return GrammarSymbol itself and NodeId
                            .map(|id| (*symbol, id))
                    })
                    // Iter<Item=Result<...>> can be collected to single Result<...>
                    // with Ok of collected items of Err of first encountered error.
                    .collect::<Result<_, _>>()?;

                // Tree and stack insertions must be done in reverse order.
                // Tree, when printed, should look ordered like source: first
                // sub-rules come in front.
                // Stack, on the other hand keeps rules which must be matched
                // first on its top, which means for `Vec` representation they
                // go last. Hence the reverse.
                stack.extend(symbols_and_ids.into_iter().rev());
            }
        }
    }
    Ok(tree)
}

mod impls {
    use super::*;
    use std::error::Error as StdError;
    use std::fmt::{Display, Formatter, Result};

    impl<'a> Display for Error<'a> {
        fn fmt(&self, f: &mut Formatter) -> Result {
            match self {
                Error::FirstSetConflict {
                    ref rule,
                    ref terminal,
                    ref conflict,
                } => {
                    writeln!(f)?;
                    writeln!(
                        f,
                        "First Set conflict for rule {} at terminal {}.",
                        rule.to_str(),
                        terminal.to_str(),
                    )?;
                    writeln!(f)?;
                    writeln!(f, "Note: conflicting productions are:")?;

                    for production in conflict {
                        let s = production
                            .iter()
                            .map(GrammarSymbol::to_str)
                            .collect::<Vec<_>>()
                            .join(" ");
                        writeln!(f, "\t{}", s)?;
                    }
                }
            }
            Ok(())
        }
    }

    // Just to be cool.
    impl<'a> StdError for Error<'a> {}
}

#[cfg(test)]
mod test {
    use super::*;
    use lang::{brainfuck, golang};
    use tree_util::*;

    const FILENAME: &str = "test.bnf";

    #[test]
    fn test_table() {
        let source = r#"
            <E> ::= <T> <E'>
            <E'> ::= "+" <T> <E'> | ""
            <T> ::= <F> <T'>
            <T'> ::= "*" <F> <T'> | ""
            <F> ::= "(" <E> ")" | "id"
        "#;
        let grammar = Grammar::from_str(source, FILENAME.into()).unwrap();
        let table = Table::ll1(&grammar, "E").unwrap();

        let i = table.symbol_map[&NonTerminal("E'")];
        let j = table.symbol_map[&Terminal("+")];
        let expected = GrammarProduction(vec![Terminal("+"), NonTerminal("T"), NonTerminal("E'")]);
        if let Some(ref prod) = table.table[[i, j]] {
            assert_eq!(*prod, expected);
        }
    }

    #[test]
    fn test_parser_expr() {
        let source = r#"
            <E> ::= <T> <E'>
            <E'> ::= "+" <T> <E'> | ""
            <T> ::= <F> <T'>
            <T'> ::= "*" <F> <T'> | ""
            <F> ::= "(" <E> ")" | "identifier"
        "#;
        let grammar = Grammar::from_str(source, FILENAME.into()).unwrap();
        let lexer = golang::make_lexer();
        let input = "one + two * three";
        let tokens = lexer.into_tokens(input, FILENAME.into());
        let tree = parse_tokens(&grammar, "E", tokens).unwrap();

        let expected = tree!{
          "<E>" => {
            "<T>" => {
              "<F>" => {
                "one"},
              "<T'>"},
            "<E'>" => {
              "Operator(Add)",
              "<T>" => {
                "<F>" => {
                  "two"},
                "<T'>" => {
                  "Operator(Mul)"},
                  "<F>" => {
                    "tree"},
                  "<T'>"},
              "<E'>"}}
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
        let grammar = Grammar::from_str(source, FILENAME.into()).unwrap();
        // println!("{:#?}", grammar);
        let input = ",[.-[-->++<]>+]";
        let tokens = brainfuck::make_lexer().into_tokens(input, FILENAME.into());
        let tree = parse_tokens(&grammar, "Code", tokens).unwrap();

        let code_children: Vec<_> = tree
            .children(tree.root_node_id().unwrap())
            .unwrap()
            .map(Node::data)
            .collect();
        assert_eq!(code_children, ["<Command>", "<Code>"]);

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
        let grammar = Grammar::from_str(source, FILENAME.into()).unwrap();
        let lexer = golang::make_lexer();
        let input = "id + + * id";
        let tokens = lexer.into_tokens(input, FILENAME.into());
        assert!(parse_tokens(&grammar, "E", tokens).is_err());
    }
}
