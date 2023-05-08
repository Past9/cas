use crate::parse::ast::{
    ast_helpers::{int, pow, prd},
    Ast,
};

impl Ast {
    pub(crate) fn simplify_quotient(l: Self, r: Self) -> Self {
        prd([l, pow(r, int(-1)).simplify()]).simplify()
    }
}
