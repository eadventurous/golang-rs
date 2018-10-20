use id_tree::*;
use lang::golang::*;
use syn::bnf::Grammar;
use syn::ebnf::{self, Syntax};
use syn::predictive_parser::parse_tokens;
use tree_util::*;

#[cfg(test)]
mod tests;

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

pub fn build_tree(source: &str, filename: String, verbose: bool) -> Result<Tree<String>, String> {
    let mut syntax = ebnf();
    if verbose {
        println!("{}", syntax);
    }

    let grammar = bnf(&mut syntax);
    if verbose {
        println!("{}", grammar);
    }

    let tokens = necessary_semicolon(drop_comments(make_lexer().into_tokens(source, filename)));
    let tree = parse_tokens(&grammar, "Root", tokens);
    if verbose {
        match tree {
            Ok(ref tree) => println!("{}", TreeFmt(tree)),
            Err(ref e) => println!("{}", e),
        }
    }
    tree
}
