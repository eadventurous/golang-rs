use std::fmt::Debug;
use regex::Captures;

pub mod brainfuck;
pub mod golang;

pub trait Token<'a>: Ord + Debug + Sized {
    fn describe(&self) -> String {
        format!("{:?}", self)
    }
}


pub trait TokenFactory<'a, T> where T: Token<'a>
{
    fn token(&self, c: Captures<'a>) -> T;
}

/// ```rust
/// let factory_comma = |_| Tok::Comma;
/// let factory_ident = |c| Tok::Ident(c.as_str());
/// ```
impl<'a, T, F> TokenFactory<'a, T> for F
    where
        T: Token<'a>,
        F: Fn(Captures<'a>) -> T {
    fn token(&self, c: Captures<'a>) -> T {
        self(c)
    }
}
//
///// Produce a function that constantly returns the same value ignoring the argument.
//#[inline]
//pub fn constant<T, A>(x: T) -> impl Fn(A) -> T
//    where T: Clone {
//    move |_: A| x.clone()
//}
