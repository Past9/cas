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
                return Self::from_frac(Pow::pow(base_frc.recip(), -exponent));
            }
        }

        // SINTPOW-2
        if exponent.is_zero() {
            return int(1);
        }

        // SINTPOW-3
        if exponent.is_one() {
            return base;
        }

        // SINTPOW-4
        if let Self::Pow(base_base, base_exp) = base {
            let p = prd([*base_exp, Self::Int(exponent)]).simplify();
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

#[cfg(test)]
mod tests {
    use crate::parse::ast::{ast_helpers::*, test_helpers::test_simplified_src};

    #[test]
    fn simplifies_int_power() {
        test_simplified_src("2 ^ 3", int(8));
        test_simplified_src("-2 ^ 3", int(-8));
        test_simplified_src("-2 ^ 2", int(4));
        test_simplified_src("2 ^ -3", frc(1, 8));
        test_simplified_src("-2 ^ -3", frc(-1, 8));
        test_simplified_src("-2 ^ -2", frc(1, 4));
    }

    #[test]
    fn does_not_simplify_perfect_roots() {
        // Does not become 2
        test_simplified_src("4 ^ 0.5", pow(int(4), frc(1, 2)));

        // Does not become 2
        test_simplified_src("8 ^ (1/3)", pow(int(8), frc(1, 3)));

        // Does not become 1/2
        test_simplified_src("4 ^ -0.5", pow(int(4), frc(-1, 2)));

        // Does not become 1/2
        test_simplified_src("8 ^ -(1/3)", pow(int(8), frc(-1, 3)));

        // Does not become i (imaginary number)
        test_simplified_src("-1 ^ 0.5", pow(int(-1), frc(1, 2)));

        // Does not become sqrt(2) * i (imaginary number)
        test_simplified_src("-2 ^ 0.5", pow(int(-2), frc(1, 2)));
    }

    #[test]
    fn multiplies_integer_exponents() {
        test_simplified_src("2 ^ 2 ^ 3", int(64));
        test_simplified_src("x ^ 2 ^ 3", pow(sym("x"), int(6)));
        test_simplified_src("x ^ 2 ^ -3", pow(sym("x"), int(-6)));
        test_simplified_src("x ^ 2 ^ -2", pow(sym("x"), int(-4)));
        test_simplified_src("x ^ y ^ 2", pow(sym("x"), prd([int(2), sym("y")])));
        test_simplified_src("((x ^ 0.5) ^ 0.5) ^ 8", pow(sym("x"), int(2)));
        test_simplified_src(
            "((x * y) ^ 0.5 * z ^ 2) ^ 2",
            prd([sym("x"), sym("y"), pow(sym("z"), int(4))]),
        );
    }

    #[test]
    fn does_not_multiply_fractional_exponent_of_integer_exponent() {
        // Does not become `x ^ 1` -> `x`
        test_simplified_src("x ^ 2 ^ 0.5", pow(pow(sym("x"), int(2)), frc(1, 2)));
    }
}
