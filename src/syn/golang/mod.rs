use id_tree::*;
use lang::golang::*;
use syn::bnf::Grammar;
use syn::ebnf::{self, Syntax};
use syn::predictive_parser::parse_tokens;

pub fn ebnf() -> Syntax {
    let source = include_str!("golang.bnf");
    let syntax = ebnf::Parser::new(source, "golang.bnf".into())
        .parse()
        .unwrap_or_else(|e| {
            println!("{}", e);
            panic!();
        });
    syntax
}

pub fn bnf(ebnf: &mut Syntax) -> Grammar {
    ebnf.ebnf_to_bnf(ebnf::Recursion::Right)
}

pub fn build_tree(source: &str, filename: String) -> Result<Tree<String>, String> {
    let mut syntax = ebnf();
    println!("{}", syntax);
    let grammar = bnf(&mut syntax);
    println!("{}", grammar);

    let tokens = necessary_semicolon(drop_comments(make_lexer().into_tokens(source, filename)));
    parse_tokens(&grammar, "Root", tokens)
}
