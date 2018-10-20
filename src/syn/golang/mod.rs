use syn::bnf::Grammar;
use syn::ebnf::{self, Syntax};
use syn::predictive_parser::parse_tokens;
use id_tree::*;
use lang::golang::make_lexer;

pub fn ebnf() -> Syntax {
    let source = include_str!("golang.bnf");
    let syntax = ebnf::Parser::new(source, "golang.bnf").parse().unwrap();
    println!("{}", syntax);
    syntax
}

pub fn bnf(ebnf: &mut Syntax) -> Grammar {
    ebnf.ebnf_to_bnf(ebnf::Recursion::Right)
}

pub fn build_tree(source: &str) -> Result<Tree<String>, String> {
    println!("source: {}", source);
    let tokens = make_lexer().into_tokens(source);
    let mut syntax = ebnf();
    let grammar = bnf(&mut syntax);
    println!("{:?}", grammar);
    parse_tokens(&grammar, "Root", tokens)
}
