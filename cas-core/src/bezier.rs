use crate::ast::{helpers::sym, Ast};

impl Ast {
    pub fn bezier(p: Vec<Ast>) -> Self {
        let mut bez = Vec::new();
        let t = sym("t");
        let n = p.len() - 1;
        for i_usize in 0..=n {
            let n = Ast::from(n);
            let i = Ast::from(i_usize);
            bez.push(
                Self::binomial_coeff(n.clone(), i.clone())
                    * (Ast::from(1) - t.clone()).pow(n.clone() - i.clone())
                    * t.clone().pow(i.clone())
                    * p[i_usize].clone(),
            );
        }

        Ast::Sum(bez).simplify()
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        ast::{helpers::*, Ast},
        helpers::expect_ast,
    };

    #[test]
    fn beziers() {
        // Line
        assert_eq!(
            Ast::bezier(vec![sym("p0"), sym("p1")]),
            expect_ast("t * p1 + (1 - t) * p0").simplify()
        );

        // Quadratic
        assert_eq!(
            Ast::bezier(vec![sym("p0"), sym("p1"), sym("p2")]),
            expect_ast("(1 - t)^2 * p0 + 2 * (1 - t) * t * p1 + t^2 * p2").simplify()
        );

        // Cubic
        assert_eq!(
            Ast::bezier(vec![sym("p0"), sym("p1"), sym("p2"), sym("p3")]),
            expect_ast(
                "(1 - t)^3 * p0 + 3 * (1 - t)^2 * t * p1 + 3 * (1 - t) * t^2 * p2 + t^3 * p3"
            )
            .simplify()
        );
    }
}
