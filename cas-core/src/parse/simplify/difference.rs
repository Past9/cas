use crate::parse::ast::{
    ast_helpers::{neg, sum},
    Ast,
};

impl Ast {
    pub(crate) fn simplify_difference(l: Self, r: Self) -> Self {
        sum([l, neg(r).simplify()]).simplify()
    }
}
