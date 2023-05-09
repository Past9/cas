use crate::parse::ast::{
    ast_helpers::{neg, sum},
    Ast,
};

impl Ast {
    pub(crate) fn simplify_difference(l: Self, r: Self) -> Self {
        sum([l, neg(r).simplify()]).simplify()
    }
}

#[cfg(test)]
mod tests {
    use crate::parse::ast::{ast_helpers::*, test_helpers::test_simplified_src};

    #[test]
    fn simplify_const_sub() {
        test_simplified_src("3 - 2", int(1));
        test_simplified_src("2 - 3", int(-1));
        test_simplified_src("0 - 0", int(0));
        test_simplified_src("1 - 1", int(0));
        test_simplified_src("1 / 2 - 1 / 2", int(0));
        test_simplified_src("3 - 1 / 2", frc(5, 2));
        test_simplified_src("1 / 2 - 3", frc(-5, 2));
        test_simplified_src("1 / 2 - 2 / 3", frc(-1, 6));
    }

    #[test]
    fn simplify_symbol_sub() {
        test_simplified_src("x - 1", sum([int(-1), sym("x")]));
        test_simplified_src("x - y", sum([sym("x"), prd([int(-1), sym("y")])]));
        test_simplified_src("x - x", int(0));
        test_simplified_src("x - (2 * y)", sum([sym("x"), prd([int(-2), sym("y")])]));
        test_simplified_src("x - y - y", sum([sym("x"), prd([int(-2), sym("y")])]));
        test_simplified_src("x - (y + y)", sum([sym("x"), prd([int(-2), sym("y")])]));
    }
}
