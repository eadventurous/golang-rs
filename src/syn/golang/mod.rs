use id_tree::*;
use lang::golang::*;
use lex::ErrorBytes;
use syn::bnf::Grammar;
use syn::ebnf::{self, Syntax};
use syn::predictive_parser::*;
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
    ebnf.expand_into_bnf(ebnf::Recursion::Right)
}

pub fn build_tree(
    source: &str,
    filename: String,
    verbose: bool,
) -> Result<Tree<String>, ErrorBytes> {
    let mut syntax = ebnf();
    if verbose {
        println!("{}", syntax);
    }

    let grammar = bnf(&mut syntax);
    if verbose {
        println!("{}", grammar);
    }

    let tokens = necessary_semicolon(drop_comments(
        make_lexer().into_tokens(source, filename.clone()),
    ));
    let tree = parse_tokens_with_meta(&grammar, "Root", tokens, source, filename);
    if verbose {
        match tree {
            Ok(ref tree) => println!("{}", TreeFmt(tree)),
            Err(ref e) => println!("{}", e),
        }
    }
    tree
}
