use crate::parse::ast::{
    ast_helpers::{int, pow, prd},
    Ast,
};

impl Ast {
    pub(crate) fn simplify_quotient(l: Self, r: Self) -> Self {
        prd([l, pow(r, int(-1)).simplify()]).simplify()
    }
}

#[cfg(test)]
mod tests {
    use crate::parse::ast::{ast_helpers::*, test_helpers::test_simplified_src};

    #[test]
    fn simplify_const_div() {
        test_simplified_src("1 / 2", frc(1, 2));
        test_simplified_src("-1 / 2", frc(-1, 2));
        test_simplified_src("1 / -2", frc(-1, 2));
        test_simplified_src("-1 / -2", frc(1, 2));
        test_simplified_src("1 / 2 / 2", frc(1, 4));
        test_simplified_src("(1 / 2) / 2", frc(1, 4));
        test_simplified_src("1 / (2 / 2)", int(1));
        test_simplified_src("0.5 / 0.25", int(2));
        test_simplified_src("0.25 / 0.5", frc(1, 2));
    }

    #[test]
    fn simplify_symbol_div() {
        test_simplified_src("x / x", int(1));
        test_simplified_src("(x + y) / (y + x)", int(1));
        test_simplified_src("(x * y) / y", sym("x"));
        test_simplified_src("(x * y) / x", sym("y"));
        test_simplified_src("(2 * x) / x", int(2));
        test_simplified_src("(x + x) / x", int(2));
        test_simplified_src("x / (x + x)", frc(1, 2));
        test_simplified_src("(x * x) / x", sym("x"));
        test_simplified_src("x / (x * x)", pow(sym("x"), int(-1)));
        test_simplified_src("(x ^ 2) / x", sym("x"));
        test_simplified_src("x / (x ^ 2)", pow(sym("x"), int(-1)));
        test_simplified_src("x ^ 5 / x ^ 2", pow(sym("x"), int(3)));
        test_simplified_src("x ^ 2 / x ^ 5", pow(sym("x"), int(-3)));
    }
}
