use num::BigRational;

use crate::parse::ast::Ast;

impl Ast {
    pub(crate) fn simplify_fraction(frc: BigRational) -> Self {
        Self::from_frac(frc)
    }
}
