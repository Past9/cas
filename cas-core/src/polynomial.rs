use crate::{
    ast::{
        helpers::{dif, fac, int, pow, prd, quo, sum},
        Ast,
    },
    rational::NumDen,
};

use num::{bigint::ToBigInt, BigInt, BigRational, BigUint, FromPrimitive, ToPrimitive, Zero};
use std::{borrow::Borrow, collections::BTreeSet};

#[derive(PartialEq, Debug)]
pub struct GpeCoefficient {
    pub coefficient: Ast,
    pub degree: BigUint,
}
impl GpeCoefficient {
    pub fn new(coefficient: Ast, degree: BigUint) -> Self {
        Self {
            coefficient,
            degree,
        }
    }
}

#[derive(PartialEq, Debug)]
pub struct CoeffVar {
    pub coefficient: Ast,
    pub var: Ast,
}
impl CoeffVar {
    pub fn new(coefficient: Ast, var: Ast) -> Self {
        Self { coefficient, var }
    }
}

impl Ast {
    /// Returns all the general variable expressions for which `self` is a
    /// generalized polynomial expression.
    pub fn vars_gpe(&self) -> BTreeSet<Ast> {
        match self {
            // VAR-1
            Ast::Und | Ast::Int(_) | Ast::Frc(_) => BTreeSet::new(),

            // VAR-2
            pow @ Ast::Pow(base, exp) => {
                if exp.is_int() && **exp > int(1) {
                    BTreeSet::from_iter(std::iter::once((**base).clone()))
                } else {
                    BTreeSet::from_iter(std::iter::once(pow.clone()))
                }
            }

            // VAR-3
            Ast::Sum(operands) => {
                let mut set = BTreeSet::new();

                for operand in operands.iter() {
                    set.extend(operand.vars_gpe());
                }

                set
            }

            // VAR-4
            Ast::Prd(operands) => {
                let mut set = BTreeSet::new();

                for operand in operands.iter() {
                    if operand.is_sum() {
                        set.insert(operand.clone());
                    } else {
                        set.extend(operand.vars_gpe());
                    }
                }

                set
            }

            other @ (Ast::Sym(_)
            | Ast::Neg(_)
            | Ast::Fac(_)
            | Ast::Dif(_, _)
            | Ast::Quo(_, _)
            | Ast::Fun(_, _)) => BTreeSet::from_iter(std::iter::once(other.clone())),
        }
    }

    /// Returns whether `self` is a generalized monomial expression in
    /// `variables`.
    pub fn is_gme<T: Borrow<Ast>, I: IntoIterator<Item = T> + Clone>(&self, variables: I) -> bool {
        if variables
            .clone()
            .into_iter()
            .any(|var| var.borrow() == self)
        {
            return true;
        } else if let Ast::Pow(base, exp) = self {
            if variables
                .clone()
                .into_iter()
                .any(|var| var.borrow() == &**base)
                && exp.is_int()
                && **exp > int(1)
            {
                return true;
            }
        } else if let Ast::Prd(operands) = self {
            if operands.iter().any(|op| !op.is_gme(variables.clone())) {
                return false;
            } else {
                return true;
            }
        }

        variables
            .into_iter()
            .all(|var| self.is_free_of(var.borrow()))
    }

    /// Returns the degree of the generalized monomial expression in `variables`.
    /// If `self` is not a monomial in `variables`, returns `Ast::Und`.
    pub fn degree_gme<T: Borrow<Ast>, I: IntoIterator<Item = T> + Clone>(
        &self,
        variables: I,
    ) -> Ast {
        if variables
            .clone()
            .into_iter()
            .any(|var| var.borrow() == self)
        {
            return int(1);
        } else if let Ast::Pow(base, exp) = self {
            if variables
                .clone()
                .into_iter()
                .any(|var| var.borrow() == &**base)
                && exp.is_int()
                && **exp > int(1)
            {
                return (**exp).clone();
            }
        } else if let Ast::Prd(operands) = self {
            let mut degree: BigInt = 0.into();
            for operand in operands.iter() {
                match operand.degree_gme(variables.clone()) {
                    Ast::Int(deg) => degree += deg,
                    _ => {
                        return Ast::Und;
                    }
                }
            }

            return Ast::Int(degree);
        }

        if variables
            .clone()
            .into_iter()
            .all(|var| self.is_free_of(var.borrow()))
        {
            return int(0);
        } else {
            return Ast::Und;
        }
    }

    /// Returns whether `self` is a generalized polynomial expression in
    /// `variables`.
    pub fn is_gpe<T: Borrow<Ast>, I: IntoIterator<Item = T> + Clone>(&self, variables: I) -> bool {
        if !self.is_sum() {
            self.is_gme(variables)
        } else {
            if variables
                .clone()
                .into_iter()
                .any(|var| var.borrow() == self)
            {
                return true;
            }

            match self {
                Ast::Sum(ops) => ops.iter().all(|op| op.is_gme(variables.clone())),
                _ => unreachable!(),
            }
        }
    }

    /// Returns the degree of the generalized polynomial expression in `variables`.
    /// If `self` is not a polynomial in `variables`, returns `Ast::Und`.
    pub fn degree_gpe<T: Borrow<Ast>, I: IntoIterator<Item = T> + Clone>(
        &self,
        variables: I,
    ) -> Ast {
        if !self.is_sum() {
            self.degree_gme(variables)
        } else {
            if variables
                .clone()
                .into_iter()
                .any(|var| var.borrow() == self)
            {
                return int(1);
            }

            match self {
                Ast::Sum(ops) => {
                    let mut max: BigInt = 0.into();
                    for op in ops.iter() {
                        let deg = op.degree_gme(variables.clone());
                        if let Ast::Int(deg) = deg {
                            if deg > max {
                                max = deg;
                            }
                        } else {
                            return Ast::Und;
                        }
                    }

                    Ast::Int(max)
                }
                _ => unreachable!(),
            }
        }
    }

    pub fn coeff_gme(&self, variable: &Ast) -> Option<GpeCoefficient> {
        if self == variable {
            return Some(GpeCoefficient::new(int(1), 1u32.into()));
        } else if let Ast::Pow(base, exp) = self {
            if &**base == variable && exp.is_int() && **exp > int(1) {
                return Some(GpeCoefficient::new(int(1), exp.expect_uint()));
            }
        } else if let Ast::Prd(operands) = self {
            let mut out_degree: BigUint = 0u32.into();
            let mut out_coefficient = self.clone();
            for operand in operands.iter() {
                let gpe_coefficient = operand.coeff_gme(variable);
                if let Some(GpeCoefficient { degree, .. }) = gpe_coefficient {
                    if !degree.is_zero() {
                        out_degree = degree;
                        out_coefficient = quo(
                            self.clone(),
                            pow(variable.clone(), Ast::Int(out_degree.to_bigint().unwrap())),
                        )
                        .simplify();
                    }
                } else {
                    return None;
                }
            }

            return Some(GpeCoefficient::new(out_coefficient, out_degree));
        }

        if self.is_free_of(&variable) {
            Some(GpeCoefficient::new(self.clone(), 0u32.into()))
        } else {
            None
        }
    }

    pub fn coeff_gpe(&self, variable: &Ast, monomial_index: BigUint) -> Ast {
        if !self.is_sum() {
            let mono_co = self.coeff_gme(variable);
            match mono_co {
                Some(co) => {
                    if monomial_index == co.degree {
                        return co.coefficient;
                    } else {
                        return int(0);
                    }
                }
                None => {
                    return Ast::Und;
                }
            }
        } else {
            if self == variable {
                if monomial_index == 1u32.into() {
                    return int(1);
                } else {
                    return int(0);
                }
            }

            let mut co = int(0);
            for operand in self.iter_operands() {
                match operand.coeff_gme(variable) {
                    Some(gpe_co) => {
                        if gpe_co.degree == monomial_index {
                            co = sum([co, gpe_co.coefficient]).simplify();
                        }
                    }
                    None => {
                        return Ast::Und;
                    }
                }
            }

            co
        }
    }

    pub fn leading_coeff_gpe(&self, variable: &Ast) -> Ast {
        let degree = self.degree_gpe([variable]);
        match degree {
            Ast::Int(int) => {
                if int > 1.into() {
                    self.coeff_gpe(variable, int.to_biguint().unwrap())
                } else {
                    Ast::Und
                }
            }
            _ => Ast::Und,
        }
    }

    pub fn coeff_var_gme<T: Borrow<Ast>, I: IntoIterator<Item = T> + Clone>(
        &self,
        variables: I,
    ) -> Option<CoeffVar> {
        if variables
            .clone()
            .into_iter()
            .any(|var| var.borrow() == self)
        {
            return Some(CoeffVar::new(int(1), self.clone()));
        } else if let Ast::Pow(base, exp) = self {
            if variables
                .clone()
                .into_iter()
                .any(|var| var.borrow() == &**base)
                && exp.is_int()
                && **exp > int(1)
            {
                return Some(CoeffVar::new(
                    int(1),
                    pow((**base).clone(), (**exp).clone()),
                ));
            }
        } else if let Ast::Prd(operands) = self {
            let mut co_parts = Vec::new();
            let mut var_parts = Vec::new();
            for operand in operands.iter() {
                if let Some(CoeffVar { coefficient, var }) =
                    operand.coeff_var_gme(variables.clone())
                {
                    co_parts.push(coefficient);
                    var_parts.push(var)
                } else {
                    return None;
                }
            }

            return Some(CoeffVar::new(
                Ast::Prd(co_parts).simplify(),
                Ast::Prd(var_parts).simplify(),
            ));
        }

        if variables
            .into_iter()
            .all(|var| self.is_free_of(var.borrow()))
        {
            Some(CoeffVar::new(self.clone(), int(1)))
        } else {
            None
        }
    }

    pub fn collect_terms<T: Borrow<Ast>, I: IntoIterator<Item = T> + Clone>(
        self,
        variables: I,
    ) -> Ast {
        if !self.is_sum() {
            if self.coeff_var_gme(variables).is_none() {
                Ast::Und
            } else {
                self
            }
        } else {
            if variables
                .clone()
                .into_iter()
                .any(|var| var.borrow() == &self)
            {
                return self;
            }

            let mut t: Vec<CoeffVar> = Vec::new();
            let mut n = 0;
            for operand in self.iter_operands() {
                if let Some(CoeffVar { coefficient, var }) =
                    operand.coeff_var_gme(variables.clone())
                {
                    let mut j = 1;
                    let mut combined = false;
                    while !combined && j <= n {
                        if var == t[j - 1].var {
                            t[j - 1] = CoeffVar::new(
                                sum([coefficient.clone(), t[j - 1].coefficient.clone()]).simplify(),
                                var.clone(),
                            );
                            combined = true;
                        }
                        j += 1;
                    }

                    if !combined {
                        t.push(CoeffVar::new(coefficient, var));
                        n += 1;
                    }
                } else {
                    return Ast::Und;
                }
            }

            let mut v = Vec::new();
            for operand in t.into_iter() {
                v.push(prd([operand.coefficient, operand.var]));
            }

            return Ast::Sum(v).simplify();
        }
    }

    pub fn algebraic_expand(self) -> Self {
        if let Some(NumDen { num, den }) = self.num_den() {
            //println!("D1 {:?}", den);
            //println!("D2 {:?}", den.do_algebraic_expand());
            quo(num.do_algebraic_expand(), den.do_algebraic_expand()).simplify()
        } else {
            Ast::Und
        }
    }

    fn do_algebraic_expand(self) -> Self {
        match self {
            Ast::Sum(operands) => {
                let mut iter = operands.into_iter();
                sum([
                    iter.next().unwrap().algebraic_expand(),
                    Ast::Sum(Vec::from_iter(iter)).simplify().algebraic_expand(),
                ])
                .simplify()
            }
            Ast::Prd(operands) => {
                let mut iter = operands.into_iter();
                Self::expand_product(
                    iter.next().unwrap().algebraic_expand(),
                    Ast::Prd(Vec::from_iter(iter)).simplify().algebraic_expand(),
                )
                .simplify()
            }
            Ast::Pow(base, exp) => {
                if let Ast::Int(ref int) = *exp {
                    if int >= &BigInt::from_i32(2).unwrap() {
                        return Self::expand_posint_power(
                            base.algebraic_expand(),
                            int.to_biguint().unwrap(),
                        );
                    }
                } else if let Ast::Frc(ref frc) = *exp {
                    let floor = frc.floor();
                    let remainder = frc - floor.clone();

                    if floor >= BigRational::from_i32(2).unwrap() {
                        return prd([
                            pow(*base.clone(), Ast::from_frac(floor))
                                .simplify()
                                .algebraic_expand(),
                            pow(*base, Ast::from_frac(remainder))
                                .simplify()
                                .algebraic_expand(),
                        ])
                        .simplify()
                        .algebraic_expand();
                    }
                }

                Ast::Pow(base, exp)
            }
            Ast::Fun(name, args) => Ast::Fun(
                name,
                args.into_iter().map(|arg| arg.algebraic_expand()).collect(),
            ),
            _ => self,
        }
        .simplify()
    }

    fn expand_product(r: Ast, s: Ast) -> Ast {
        if let Ast::Sum(operands) = r {
            let mut iter = operands.into_iter();
            sum([
                Self::expand_product(iter.next().unwrap(), s.clone()),
                Self::expand_product(Ast::Sum(Vec::from_iter(iter)).simplify(), s),
            ])
            .simplify()
            .algebraic_expand()
        } else if s.is_sum() {
            Self::expand_product(s, r)
        } else {
            prd([r, s])
        }
        .simplify()
    }

    fn expand_posint_power(u: Ast, n: BigUint) -> Ast {
        if let Ast::Sum(operands) = u {
            let mut iter = operands.into_iter();
            let first = iter.next().unwrap();
            let rest = Vec::from_iter(iter);
            let mut s = Vec::new();
            for i in 0..=n.to_i128().unwrap() {
                let k = BigUint::from_i128(i).unwrap();
                let c = quo(
                    fac(Ast::from_biguint(n.clone())).simplify(),
                    prd([
                        fac(Ast::from_biguint(k.clone())),
                        fac(dif(
                            Ast::from_biguint(n.clone()),
                            Ast::from_biguint(k.clone()),
                        )),
                    ]),
                )
                .simplify();
                s.push(Self::expand_product(
                    prd([
                        c,
                        pow(
                            first.clone(),
                            dif(Ast::from_biguint(n.clone()), Ast::from_biguint(k.clone())),
                        ),
                    ])
                    .simplify(),
                    Self::expand_posint_power(Ast::Sum(rest.clone()).simplify(), k.clone()),
                ));
            }
            Ast::Sum(s).simplify().algebraic_expand()
        } else {
            pow(u, Ast::from_biguint(n))
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use crate::{ast::helpers::*, helpers::expect_ast, polynomial::CoeffVar};

    #[test]
    fn identifies_monomial_gpe() {
        assert!(expect_ast("a * x ^ 2 * y ^ 2")
            .simplify()
            .is_gme(&[sym("x"), sym("y")]));

        assert!(!expect_ast("x ^ 2 + y ^ 2")
            .simplify()
            .is_gme(&[sym("x"), sym("y")]));

        assert!(!expect_ast("x / y").simplify().is_gme(&[sym("x"), sym("y")]));

        assert!(expect_ast("(a + b)")
            .simplify()
            .is_gme(&[sum([sym("a"), sym("b")])]));

        assert!(expect_ast("(a + b) ^ 2")
            .simplify()
            .is_gme(&[sum([sym("a"), sym("b")])]));
    }

    #[test]
    fn identifies_polynomial_gpe() {
        assert!(expect_ast("x ^ 2 + y ^ 2")
            .simplify()
            .is_gpe(&[sym("x"), sym("y")]));

        assert!(expect_ast("sin(x) ^ 2 + 2 * sin(x) + 3")
            .simplify()
            .is_gpe(&[fun("sin", [sym("x")])]));

        assert!(!expect_ast("(x / y) + (2 * y)")
            .simplify()
            .is_gpe(&[sym("x"), sym("y")]));

        assert!(!expect_ast("(x + 1) * (x + 3)")
            .simplify()
            .is_gpe(&[sym("x")]));

        assert!(expect_ast("a + b")
            .simplify()
            .is_gpe(&[sum([sym("a"), sym("b")])]));

        assert!(expect_ast("(a + b) ^ 2")
            .simplify()
            .is_gpe(&[sum([sym("a"), sym("b")])]));
    }

    #[test]
    fn gets_variables() {
        assert_eq!(
            expect_ast("x ^ 3 + 3 * x ^ 2 * y + 3 * x * y ^ 2 + y ^ 3")
                .simplify()
                .vars_gpe(),
            BTreeSet::from([sym("x"), sym("y")])
        );

        assert_eq!(
            expect_ast("3 * x * (x + 1) * y ^ 2 * z ^ n")
                .simplify()
                .vars_gpe(),
            BTreeSet::from([
                sym("x"),
                sum([int(1), sym("x")]),
                sym("y"),
                pow(sym("z"), sym("n"))
            ])
        );

        assert_eq!(
            expect_ast("a * sin(x) ^ 2 + 2 * b * sin(x) + 3 * c")
                .simplify()
                .vars_gpe(),
            BTreeSet::from([sym("a"), sym("b"), sym("c"), fun("sin", [sym("x")])])
        );

        assert_eq!(expect_ast("1/2").simplify().vars_gpe(), BTreeSet::new());

        assert_eq!(
            expect_ast("2 ^ (1/2) * x ^ 2 + 3 ^ (1/2) * x + 5 ^ (1/2)")
                .simplify()
                .vars_gpe(),
            BTreeSet::from([
                sym("x"),
                pow(int(2), frc(1, 2)),
                pow(int(3), frc(1, 2)),
                pow(int(5), frc(1, 2)),
            ])
        );
    }

    #[test]
    fn gets_monomial_degree() {
        assert_eq!(
            expect_ast("3 * w * x^2 * y^3 * z^4")
                .simplify()
                .degree_gme(&[sym("x"), sym("z")]),
            int(6)
        );
    }

    #[test]
    fn gets_polynomial_degree() {
        assert_eq!(
            expect_ast("3 * w * x^2 * y^3 * z^4")
                .simplify()
                .degree_gpe(&[sym("x"), sym("z")]),
            int(6)
        );

        assert_eq!(
            expect_ast("a * x^2 + b * x + c")
                .simplify()
                .degree_gpe(&[sym("x")]),
            int(2)
        );

        assert_eq!(
            expect_ast("a * sin(x)^2 + b * sin(x) + c")
                .simplify()
                .degree_gpe(&[fun("sin", [sym("x")])]),
            int(2)
        );

        assert_eq!(
            expect_ast("2 * x^2 * y * z^3 + w * x * z^6")
                .simplify()
                .degree_gpe(&[sym("x"), sym("z")]),
            int(7)
        );
    }

    #[test]
    fn total_degree() {
        let ast = expect_ast("a * x^2 + b * x + c").simplify();
        let vars = ast.vars_gpe();

        assert_eq!(
            vars,
            BTreeSet::from([sym("a"), sym("b"), sym("c"), sym("x"),])
        );

        assert_eq!(
            ast.degree_gpe(&vars.into_iter().collect::<Vec<_>>()),
            int(3)
        );
    }

    #[test]
    fn gets_coefficient_gpe() {
        assert_eq!(
            expect_ast("a * x^2 + b * x + c")
                .simplify()
                .coeff_gpe(&sym("x"), 2u32.into()),
            sym("a")
        );

        assert_eq!(
            expect_ast("3 * x * y^2 + 5 * x^2 * y + 7 * x + 9")
                .simplify()
                .coeff_gpe(&sym("x"), 1u32.into()),
            // 3 * y^2 + 7
            sum([int(7), prd([int(3), pow(sym("y"), int(2))])])
        );

        assert_eq!(
            expect_ast("3 * x * y^2 + 5 * x^2 * y + 7 * x + 9")
                .simplify()
                .coeff_gpe(&sym("x"), 3u32.into()),
            int(0)
        );

        assert_eq!(
            expect_ast("(3 * sin(x)) * x^2 + (2 * ln(x)) * x + 4")
                .simplify()
                .coeff_gpe(&sym("x"), 2u32.into()),
            und()
        );

        // Composition: Coefficient of `x * y^2` in the polynomial below is 3.
        // Order of coefficient_gpe calls doesn't matter here.
        assert_eq!(
            expect_ast("3 * x * y^2 + 5 * x^2 * y + 7 * x + 9")
                .simplify()
                .coeff_gpe(&sym("x"), 1u32.into())
                .coeff_gpe(&sym("y"), 2u32.into()),
            int(3)
        );

        // Coefficient of `ln(x) * x`.
        // Order of coefficient_gpe calls is significant because of
        // dependencies between generalized variables.
        assert_eq!(
            expect_ast("3 * sin(x) * x^2 + 2 * ln(x) * x + 4")
                .simplify()
                .coeff_gpe(&fun("ln", [sym("x")]), 1u32.into())
                .coeff_gpe(&sym("x"), 1u32.into()),
            int(2)
        );
    }

    #[test]
    fn gets_leading_coefficient_gpe() {
        assert_eq!(
            expect_ast("3 * x * y^2 + 5 * x^2 * y + 7 * x^2 * y^3 + 9")
                .simplify()
                .leading_coeff_gpe(&sym("x")),
            // 5 * y + 7 * y^3
            sum([
                prd([int(5), sym("y")]),
                prd([int(7), pow(sym("y"), int(3))])
            ])
        );
    }

    #[test]
    fn gets_coefficient_and_var_parts_from_monomial() {
        assert_eq!(
            expect_ast("a * x ^ 2 * y ^ 2")
                .simplify()
                .coeff_var_gme(&[sym("x"), sym("y")]),
            Some(CoeffVar::new(
                sym("a"),
                prd([pow(sym("x"), int(2)), pow(sym("y"), int(2)),])
            ))
        );

        assert_eq!(
            expect_ast("x ^ 2 + y ^ 2")
                .simplify()
                .coeff_var_gme(&[sym("x"), sym("y")]),
            None
        );

        assert_eq!(
            expect_ast("x / y")
                .simplify()
                .coeff_var_gme(&[sym("x"), sym("y")]),
            None
        );

        assert_eq!(
            expect_ast("x / y").simplify().coeff_var_gme(&[sym("y")]),
            None
        );

        assert_eq!(
            expect_ast("x / y").simplify().coeff_var_gme(&[sym("x")]),
            Some(CoeffVar::new(pow(sym("y"), int(-1)), sym("x")))
        );

        assert_eq!(
            expect_ast("(a + b)")
                .simplify()
                .coeff_var_gme(&[sum([sym("a"), sym("b")])]),
            Some(CoeffVar::new(int(1), sum([sym("a"), sym("b")])))
        );

        assert_eq!(
            expect_ast("(a + b) ^ 2")
                .simplify()
                .coeff_var_gme(&[sum([sym("a"), sym("b")])]),
            Some(CoeffVar::new(
                int(1),
                pow(sum([sym("a"), sym("b")]), int(2))
            ))
        );

        assert_eq!(
            expect_ast("x^2 * 3 * y * (a + b) ^ 2")
                .simplify()
                .coeff_var_gme(&[sum([sym("a"), sym("b")])]),
            Some(CoeffVar::new(
                prd([int(3), pow(sym("x"), int(2)), sym("y")]),
                pow(sum([sym("a"), sym("b")]), int(2))
            ))
        );
    }

    #[test]
    fn collects_terms() {
        assert_eq!(
            expect_ast("2 * a * x * y + 3 * b * x * y + 4 * a * x + 5 * b * x")
                .simplify()
                .collect_terms(&[sym("x"), sym("y")]),
            expect_ast("(2 * a + 3 * b) * x * y + (4 * a + 5 * b) * x").simplify()
        );

        assert_eq!(
            expect_ast("2 * a * x * y + 3 * b * x * y + 4 * a * x + 5 * b * x")
                .simplify()
                .collect_terms(&[sym("a"), sym("b")]),
            expect_ast("(2 * x * y + 4 * x) * a + (3 * x * y + 5 * x) * b").simplify()
        );
    }

    #[test]
    fn algebraic_expand_full() {
        assert_eq!(
            expect_ast("(x * (y + 1)^(3/2) + 1) * (x * (y + 1)^(3/2) - 1)")
                .simplify()
                .algebraic_expand(),
            expect_ast("x^2 * y^3 + 3 * x^2 * y^2 + 3 * x^2 * y + x^2 - 1").simplify()
        );

        assert_eq!(
            expect_ast("(x * (y + 1)^(1/2) + 1)^4")
                .simplify()
                .algebraic_expand(),
            expect_ast("x^4 * y^2 + 2 * x^4 * y + x^4 + 4 * x^3 * (y + 1)^(3/2) + 6 * x^2 * y + 6 * x^2 + 4 * x * (y + 1) ^ (1/2) + 1").simplify()
        );

        assert_eq!(
            expect_ast("a / ((x + 1) * (x + 2))")
                .simplify()
                .algebraic_expand(),
            expect_ast("a / (x^2 + 3 * x + 2)").simplify()
        );

        // Denominator becomes 0, so expression is 1/0, or undefined
        assert_eq!(
            expect_ast("1 / (x^2 + x - x * (x + 1))")
                .simplify()
                .algebraic_expand(),
            und()
        );

        assert_eq!(
            expect_ast("1 / (x^2 + 1 - x * (x + 1))")
                .simplify()
                .algebraic_expand(),
            expect_ast("1 / (1 - x)").simplify()
        );

        assert_eq!(
            expect_ast("sin(a * (b + c))").simplify().algebraic_expand(),
            expect_ast("sin(a * b + a * c)").simplify()
        );

        assert_eq!(
            expect_ast("a / (b * (c + d))")
                .simplify()
                .algebraic_expand(),
            expect_ast("a / (b * c + b * d)").simplify()
        );

        assert_eq!(
            expect_ast("(x + 1)^(5/2)").simplify().algebraic_expand(),
            expect_ast("(x + 1)^(1/2) * x^2 + 2 * (x + 1)^(1/2) * x + (x + 1)^(1/2)").simplify()
        );
    }
}
