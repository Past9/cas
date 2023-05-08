use num::BigRational;

use crate::parse::ast::Ast;

impl Ast {
    pub(crate) fn simplify_fraction(frc: BigRational) -> Self {
        Self::from_frac(frc)
    }
}

#[cfg(test)]
mod tests {
    use crate::parse::ast::{ast_helpers::*, test_helpers::test_simplified_src};

    #[test]
    fn simplifies_fraction() {
        test_simplified_src("0.5", frc(1, 2));
        test_simplified_src("0 / 10", int(0));
        test_simplified_src("20 / 10", int(2));
    }
}
