use ::{Lexer, LexerBuilder, TokenFactory};
use regex::Match;
use super::Token;

pub use self::BfToken::*;

#[derive(Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Debug)]
pub enum BfToken<'a> {
    Left,
    Right,
    Cond,
    Loop,
    Input,
    Output,
    Inc,
    Dec,
    Comment(&'a str),
}

impl<'a> Token<'a> for BfToken<'a> {}


pub fn make_lexer<'a>() -> Lexer<'a, BfToken<'a>> {
    let constant = |x| { move |_| x };
    LexerBuilder::new()
        .add(r"<", constant(BfToken::Left))
        .add(r">", constant(BfToken::Right))
        .add(r"\[", constant(BfToken::Cond))
        .add(r"]", constant(BfToken::Loop))
        .add(r",", constant(BfToken::Input))
        .add(r"\.", constant(BfToken::Output))
        .add(r"\+", constant(BfToken::Inc))
        .add(r"-", constant(BfToken::Dec))
        .add(r"[^<>\[\],.+\-]+", |m| BfToken::Comment(m.as_str()))
        .build()
}


#[cfg(test)]
mod test {
    use super::*;
    use ::engine;

    #[test]
    fn brainfuck() {
        let source = &r#"++L[>+<-].End"#[..];

        let tokens = engine(&make_lexer(), source).unwrap();
        assert_eq!(tokens, vec![Inc, Inc, Comment("L"), Cond, Right, Inc, Left, Dec, Loop, Output, Comment("End")]);
    }
}
