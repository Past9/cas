use crate::parse::ast::{
    ast_helpers::{int, pow, prd},
    Ast,
};
use num::{traits::Pow, BigInt, BigRational, One, Signed, Zero};

impl Ast {
    pub(crate) fn simplify_power(base: Self, exponent: Self) -> Self {
        // SPOW-1
        if base.is_undefined() || exponent.is_undefined() {
            return Ast::Und;
        }

        // SPOW-2
        if base.is_int_zero() {
            if exponent.is_pos_const() {
                return int(0);
            } else {
                return Ast::Und;
            }
        }

        // SPOW-3
        if base.is_int_one() {
            return base;
        }

        // SPOW-4
        if let Ast::Int(int) = exponent {
            return Self::simplify_integer_power(base, int);
        }

        // SPOW-5
        pow(base, exponent)
    }

    fn simplify_integer_power(base: Self, exponent: BigInt) -> Self {
        // SINTPOW-2
        if exponent.is_zero() {
            return int(1);
        }

        // SINTPOW-3
        if exponent.is_one() {
            return base;
        }

        // SINTPOW-1
        if let Self::Int(base_int) = &base {
            if exponent.is_positive() {
                return Self::Int(Pow::pow(base_int, exponent.to_biguint().unwrap()));
            } else if exponent.is_negative() {
                return Self::from_frac(BigRational::new(
                    BigInt::one(),
                    Pow::pow(base_int, (-exponent).to_biguint().unwrap()),
                ));
            }
        }

        if let Self::Frc(base_frc) = &base {
            if exponent.is_positive() {
                return Self::from_frac(Pow::pow(base_frc, exponent));
            } else if exponent.is_negative() {
                return Self::from_frac(Pow::pow(base_frc.recip(), exponent));
            }
        }

        // SINTPOW-4
        if let Self::Pow(base_base, base_exp) = base {
            let p = prd(*base_exp, Self::Int(exponent)).simplify();
            if let Self::Int(p) = p {
                // SINTPOW-4-1
                return Self::simplify_integer_power(*base_base, p);
            } else {
                // SINTPOW-4-2
                return pow(*base_base, p).simplify();
            }
        }

        // SINTPOW-5
        if let Self::Prd(factors) = base {
            return Self::Prd(
                factors
                    .into_iter()
                    .map(|factor| pow(factor, Self::Int(exponent.clone())).simplify())
                    .collect(),
            )
            .simplify();
        }

        // SINTPOW-6
        pow(base, Self::Int(exponent))
    }
}
