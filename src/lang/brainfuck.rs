use lex::{Lexer, LexerBuilder, Token};

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

impl<'a> Token<'a> for BfToken<'a> {
    fn descriptor(&self) -> &'static str {
        match *self {
            Left => "Left",
            Right => "Right",
            Cond => "Cond",
            Loop => "Loop",
            Input => "Input",
            Output => "Output",
            Inc => "Inc",
            Dec => "Dec",
            Comment(..) => "Comment",
        }
    }
}


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
        .add(r"[^<>\[\],.+\-]+", |c| BfToken::Comment(c.get(0).unwrap().as_str()))
        .build()
}


#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn brainfuck() {
        let source = &r#"++L[>+<-].End"#[..];

        let tokens = make_lexer()
            .into_tokens(source)
            .filter_map(Result::ok)
            .map(|meta| meta.token)
            .collect::<Vec<_>>();
        assert_eq!(tokens, vec![Inc, Inc, Comment("L"), Cond, Right, Inc, Left, Dec, Loop, Output, Comment("End")]);
    }
}
