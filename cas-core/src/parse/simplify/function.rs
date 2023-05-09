use crate::parse::ast::Ast;

impl Ast {
    pub(crate) fn simplify_function(name: String, args: Vec<Ast>) -> Self {
        if args.iter().any(Ast::is_undefined) {
            return Ast::Und;
        }

        Ast::Fun(name, args)
    }
}

#[cfg(test)]
mod tests {
    use crate::parse::ast::{ast_helpers::*, test_helpers::test_simplified_src};

    #[test]
    fn simplifies_args() {
        test_simplified_src("f(1 + 3, x * x)", fun("f", [int(4), pow(sym("x"), int(2))]));
        test_simplified_src(
            "f(1 + 3, g(x * x))",
            fun("f", [int(4), fun("g", [pow(sym("x"), int(2))])]),
        );
    }

    #[test]
    fn hoists_undefined() {
        test_simplified_src("f(undefined)", und());
        test_simplified_src("f(1 + 3, x * undefined)", und());
        test_simplified_src("f(1 + 3, g(x * undefined))", und());
    }
}
