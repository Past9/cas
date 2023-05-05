use std::collections::BTreeMap;

use parse::ast::Ast;

mod error;
//pub mod expr;
mod parse;
mod simplify;
mod tokenize;

pub type Span = std::ops::Range<usize>;

#[derive(Debug, Clone, PartialEq)]
pub struct Spanned<T> {
    pub inner: T,
    pub span: Span,
}
impl<T> Spanned<T> {
    pub fn new(inner: T, span: Span) -> Self {
        Self { inner, span }
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Operands {
    operands: BTreeMap<Ast, usize>,
}
impl Operands {
    fn empty() -> Self {
        Self {
            operands: BTreeMap::new(),
        }
    }

    pub fn from<const N: usize>(operands: [Ast; N]) -> Self {
        let mut ops = Self::empty();
        operands.into_iter().for_each(|op| ops.insert(op));
        ops
    }

    pub fn insert(&mut self, operand: Ast) {
        *self.operands.entry(operand).or_insert(1) += 1;
    }
}
