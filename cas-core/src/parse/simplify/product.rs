use std::borrow::Cow;

use num::BigRational;

use crate::parse::ast::{
    ast_helpers::{int, prd},
    Ast,
};

impl Ast {
    pub(crate) fn simplify_product(operands: Vec<Ast>) -> Self {
        if operands.len() == 0 {
            return int(1);
        }

        // SPRD-1
        if operands.iter().any(Ast::is_undefined) {
            return Ast::Und;
        }

        // SPRD-2
        if operands.iter().any(Ast::is_int_zero) {
            return int(0);
        }

        // SPRD-3
        if operands.len() == 1 {
            return operands.into_iter().next().unwrap();
        }

        // SPRD-4
        let operands = Self::simplify_product_rec(operands);

        // SPRD-4-3
        if operands.len() == 0 {
            return int(1);
        }

        // SPRD-4-1
        if operands.len() == 1 {
            return operands.into_iter().next().unwrap();
        }

        // SPRD-4-2
        if operands.len() >= 2 {
            return Self::Prd(operands);
        }

        unreachable!()
    }

    fn simplify_product_rec(operands: Vec<Ast>) -> Vec<Ast> {
        if operands.len() < 2 {
            panic!("At least 2 operands required");
        }

        // SPRDREC-1
        if operands.len() == 2 && !operands[0].is_product() && !operands[1].is_product() {
            // SPRDREC-1-1
            let mut operands = {
                let (operands, both_consts) = match (&operands[0], &operands[1]) {
                    (Ast::Int(l), Ast::Int(r)) => (vec![Self::Int(l * r)], true),
                    (Ast::Frc(l), Ast::Frc(r)) => (vec![Self::from_frac(l * r)], true),

                    (Ast::Int(int), Ast::Frc(frc)) | (Ast::Frc(frc), Ast::Int(int)) => (
                        vec![Self::from_frac(
                            BigRational::from_integer(int.clone()) * frc,
                        )],
                        true,
                    ),

                    _ => (operands, false),
                };

                if both_consts {
                    if operands.len() == 1 && operands[0].is_int_one() {
                        return vec![];
                    } else {
                        return operands;
                    }
                }

                operands
            };

            // SPRDREC-1-2
            {
                if operands[0].is_int_one() {
                    return vec![operands.swap_remove(1)];
                }

                if operands[1].is_int_one() {
                    return vec![operands.into_iter().next().unwrap()];
                }
            };

            // SPRDREC-1-3
            {
                let (base_l, exp_l) = operands[0].as_power_operands();
                let (base_r, exp_r) = operands[1].as_power_operands();

                if base_l == base_r {
                    let exp = Self::simplify_sum(vec![exp_l.into_owned(), exp_r.into_owned()]);
                    let pow = Self::simplify_power(base_l.into_owned(), exp);

                    if pow.is_int_one() {
                        return vec![];
                    } else {
                        return vec![pow];
                    }
                }
            };

            // SPRDREC-1-4
            {
                if operands[1] < operands[0] {
                    operands.reverse();
                    return operands;
                }
            };

            // SPRDREC-1-5
            {
                return operands;
            };
        }

        // SPRDREC-2
        if operands.len() == 2 && (operands[0].is_product() || operands[1].is_product()) {
            let mut iter = operands.into_iter();

            let l = iter.next().unwrap();
            let r = iter.next().unwrap();

            return match (l, r) {
                // SPRDREC-2-1
                (Ast::Prd(l), Ast::Prd(r)) => Self::merge_products(l, r),
                // SPRDREC-2-2
                (Ast::Prd(l), r) => Self::merge_products(l, vec![r]),
                // SPRDREC-2-3
                (l, Ast::Prd(r)) => Self::merge_products(vec![l], r),
                _ => unreachable!(),
            };
        }

        // SPRDREC-3
        let mut iter = operands.into_iter();
        let first = iter.next().unwrap();
        let remaining = Self::simplify_product_rec(iter.collect());

        match first {
            // SPRDREC-3-1
            Ast::Prd(operands) => Self::merge_products(operands, remaining),
            // SPRDREC-3-2
            operand => Self::merge_products(vec![operand], remaining),
        }
    }

    fn merge_products(p: Vec<Ast>, q: Vec<Ast>) -> Vec<Ast> {
        // MPRD-1
        if q.len() == 0 {
            return p;
        }

        // MPRD-2
        if p.len() == 0 {
            return q;
        }

        // MPRD-3
        {
            let mut p_iter = p.clone().into_iter();
            let p1 = p_iter.next().unwrap();
            let remaining_p = p_iter.collect::<Vec<_>>();

            let mut q_iter = q.clone().into_iter();
            let q1 = q_iter.next().unwrap();
            let remaining_q = q_iter.collect::<Vec<_>>();

            let mut h = Self::simplify_product_rec(vec![p1.clone(), q1.clone()]);

            // MPRD-3-1
            if h.len() == 0 {
                return Self::merge_products(remaining_p, remaining_q);
            }

            // MPRD-3-2
            if h.len() == 1 {
                let mut merged = Self::merge_products(remaining_p, remaining_q);
                h.append(&mut merged);
                return h;
            }

            if h.len() == 2 {
                // MPRD-3-3
                if h[0] == p1 && h[1] == q1 {
                    return std::iter::once(p1)
                        .chain(Self::merge_products(remaining_p, q).into_iter())
                        .collect();
                }

                // MPRD-3-4
                if h[0] == q1 && h[1] == p1 {
                    return std::iter::once(q1)
                        .chain(Self::merge_products(p, remaining_q))
                        .into_iter()
                        .collect();
                }
            }
        }

        unreachable!()
    }

    /// Returns a representation of `self` as a base and exponent.
    /// If `self` is `Ast::Pow`, returns `(base, exponent)`.
    /// Otherwise returns `(self, 1)`.
    fn as_power_operands(&self) -> (Cow<Ast>, Cow<Ast>) {
        match self {
            operand @ (Ast::Und
            | Ast::Sym(_)
            | Ast::Int(_)
            | Ast::Frc(_)
            | Ast::Neg(_)
            | Ast::Fac(_)
            | Ast::Sum(_)
            | Ast::Prd(_)
            | Ast::Dif(_, _)
            | Ast::Fun(_, _)
            | Ast::Quo(_, _)) => (Cow::Borrowed(operand), Cow::Owned(int(1))),
            Ast::Pow(base, exp) => (Cow::Borrowed(base), Cow::Borrowed(exp)),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::parse::ast::{ast_helpers::*, test_helpers::test_simplified_src};

    #[test]
    fn simplify_const_mul() {
        test_simplified_src("1 * 2", int(2));
        test_simplified_src("0.5 * 2", int(1));
        test_simplified_src("0.5 * 3", frc(3, 2));
    }

    #[test]
    fn simplify_symbol_mul() {
        test_simplified_src("0.5 * x * 3", prd([frc(3, 2), sym("x")]));
        test_simplified_src("0.5 * -x * 3", prd([frc(-3, 2), sym("x")]));
        test_simplified_src("(x / 1) * (1 / x)", int(1));
        test_simplified_src("x * y * x", prd([pow(sym("x"), int(2)), sym("y")]));
        test_simplified_src("x * y * x ^ 2", prd([pow(sym("x"), int(3)), sym("y")]));
        test_simplified_src("y * x * y", prd([sym("x"), pow(sym("y"), int(2))]));
    }

    #[test]
    fn does_not_distribute_const_over_sum() {
        test_simplified_src("2 * (3 + x)", prd([int(2), sum([int(3), sym("x")])]));
        test_simplified_src("2 * (x + y)", prd([int(2), sum([sym("x"), sym("y")])]));
        test_simplified_src(
            "2 * (x + y - 3 + 2 * z)",
            prd([
                int(2),
                sum([int(-3), sym("x"), sym("y"), prd([int(2), sym("z")])]),
            ]),
        );
        test_simplified_src(
            "2 * (3 + x) * (4 + x)",
            prd([int(2), sum([int(3), sym("x")]), sum([int(4), sym("x")])]),
        );

        test_simplified_src(
            "2 * (3 + x) * (4 + x) * (5 + x)",
            prd([
                int(2),
                sum([int(3), sym("x")]),
                sum([int(4), sym("x")]),
                sum([int(5), sym("x")]),
            ]),
        );

        test_simplified_src(
            "2 * (3 + x) * (4 + x) * (5 + x)",
            prd([
                int(2),
                sum([int(3), sym("x")]),
                sum([int(4), sym("x")]),
                sum([int(5), sym("x")]),
            ]),
        );
    }

    #[test]
    fn adds_powers() {
        test_simplified_src("x ^ 2 * x ^ 3", pow(sym("x"), int(5)));
        test_simplified_src("x ^ 3 * x ^ -2", sym("x"));
        test_simplified_src("x ^ 2 * x ^ -3", pow(sym("x"), int(-1)));
        test_simplified_src("x ^ 3 * x ^ -3", int(1));
    }

    #[test]
    fn div_mul_ltr() {
        // Ensures multiplication and division are parsed left-to-right at the same precedence
        // instead of prioritizing one over the other, which can give incorrect/unexpected results.
        test_simplified_src("2 * 3 / 4 * 5", frc(15, 2));
        test_simplified_src("2 / 3 * 4 / 5", frc(8, 15));
    }
}
