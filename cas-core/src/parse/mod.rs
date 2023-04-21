pub mod ast;

use std::str::FromStr;

use chumsky::{primitive::just, recursive::recursive, select, Parser, Stream};
use rust_decimal::Decimal;

use crate::{
    error::SyntaxError,
    parse::ast::UnaryOp,
    tokenize::{tokenize_src, tokens::Token},
    Spanned,
};

use self::ast::{Ast, BinaryOp};

#[derive(Debug, Clone)]
pub struct ParserResult {
    pub ast: Option<Ast>,
    pub parser_errors: Vec<SyntaxError<Token>>,
    pub tokenizer_errors: Vec<SyntaxError<char>>,
}

pub fn parse_src(src: &str) -> ParserResult {
    let tokenizer_result = tokenize_src(src);
    let len = src.chars().count();
    let (expr, parser_errors) = parse(tokenizer_result.tokens, len);

    ParserResult {
        ast: expr,
        parser_errors,
        tokenizer_errors: tokenizer_result.errors,
    }
}

pub(crate) fn parse(
    tokens: Vec<Spanned<Token>>,
    src_len: usize,
) -> (Option<Ast>, Vec<SyntaxError<Token>>) {
    let stream = Stream::from_iter(
        src_len..src_len + 1,
        tokens
            .into_iter()
            .map(|spanned| (spanned.inner, spanned.span)),
    );

    parser().parse_recovery_verbose(stream)
}

fn parser() -> impl Parser<Token, Ast, Error = SyntaxError<Token>> + Clone {
    recursive(|expr| {
        let symbol = select! {
            Token::Ident(name) => Ast::symbol(name),
        }
        .boxed();

        let constant = select! {
            Token::Const(text) => Ast::constant(
                Decimal::from_str(&text).expect(&format!("Could not parse {} as number", text))
            )
        }
        .boxed();

        let atom = symbol
            .or(constant)
            .or(expr
                .clone()
                .delimited_by(just(Token::OpenParen), just(Token::CloseParen)))
            .boxed();

        let factorial = atom
            .then(just(Token::Bang).repeated())
            .foldl(|operand, op| Ast::unary_op(UnaryOp::from_token(op), operand))
            .boxed();

        let neg = just(Token::Minus)
            .repeated()
            .then(factorial)
            .foldr(|op, operand| Ast::unary_op(UnaryOp::from_token(op), operand))
            .boxed();

        let exp = neg
            .clone()
            .then(just(Token::Caret).then(neg).repeated())
            .foldl(|left, (op, right)| Ast::binary_op(BinaryOp::from_token(op), left, right))
            .boxed();

        let mul_div = exp
            .clone()
            .then(
                just(Token::Asterisk)
                    .or(just(Token::FwdSlash))
                    .then(exp)
                    .repeated(),
            )
            .foldl(|left, (op, right)| Ast::binary_op(BinaryOp::from_token(op), left, right))
            .boxed();

        let add_sub = mul_div
            .clone()
            .then(
                just(Token::Plus)
                    .or(just(Token::Minus))
                    .then(mul_div)
                    .repeated(),
            )
            .foldl(|left, (op, right)| Ast::binary_op(BinaryOp::from_token(op), left, right))
            .boxed();

        add_sub
    })
}

#[cfg(test)]
mod tests {
    use crate::parse::ast::{add, con, div, exp, fac, mul, neg, sub, sym};

    use super::*;

    #[test]
    fn symbol() {
        assert_eq!(parse_src("x").ast.unwrap(), sym("x"));
    }

    #[test]
    fn neg_symbol() {
        assert_eq!(parse_src("-x").ast.unwrap(), neg(sym("x")));
    }

    #[test]
    fn double_neg() {
        assert_eq!(parse_src("--x").ast.unwrap(), neg(neg(sym("x"))));
    }

    #[test]
    fn factorial() {
        assert_eq!(parse_src("3!").ast.unwrap(), fac(con("3")));
    }

    #[test]
    fn double_factorial() {
        assert_eq!(parse_src("3!!").ast.unwrap(), fac(fac(con("3"))));
    }

    #[test]
    fn neg_factorial() {
        assert_eq!(parse_src("-3!").ast.unwrap(), neg(fac(con("3"))));
    }

    #[test]
    fn pos_integer() {
        assert_eq!(parse_src("123").ast.unwrap(), con("123"));
    }

    #[test]
    fn neg_integer() {
        assert_eq!(parse_src("-123").ast.unwrap(), neg(con("123")));
    }

    #[test]
    fn pos_decimal() {
        assert_eq!(parse_src("123.456").ast.unwrap(), con("123.456"));
    }

    #[test]
    fn neg_decimal() {
        assert_eq!(parse_src("-123.456").ast.unwrap(), neg(con("123.456")));
    }

    #[test]
    fn single_add() {
        assert_eq!(parse_src("1 + 2").ast.unwrap(), add(con("1"), con("2")));
    }

    #[test]
    fn multiple_add() {
        assert_eq!(
            parse_src("1 + 2 + 3").ast.unwrap(),
            add(add(con("1"), con("2")), con("3"))
        );
    }

    #[test]
    fn single_sub() {
        assert_eq!(parse_src("1 - 2").ast.unwrap(), sub(con("1"), con("2")));
    }

    #[test]
    fn multiple_sub() {
        assert_eq!(
            parse_src("1 - 2 - 3").ast.unwrap(),
            sub(sub(con("1"), con("2")), con("3"))
        );
    }

    #[test]
    fn add_sub() {
        assert_eq!(
            parse_src("1 + 2 - 3").ast.unwrap(),
            sub(add(con("1"), con("2")), con("3"))
        );
    }

    #[test]
    fn sub_add() {
        assert_eq!(
            parse_src("1 - 2 + 3").ast.unwrap(),
            add(sub(con("1"), con("2")), con("3"))
        );
    }

    #[test]
    fn single_mul() {
        assert_eq!(parse_src("1 * 2").ast.unwrap(), mul(con("1"), con("2")));
    }

    #[test]
    fn multiple_mul() {
        assert_eq!(
            parse_src("1 * 2 * 3").ast.unwrap(),
            mul(mul(con("1"), con("2")), con("3"))
        );
    }

    #[test]
    fn single_div() {
        assert_eq!(parse_src("1 / 2").ast.unwrap(), div(con("1"), con("2")));
    }

    #[test]
    fn multiple_div() {
        assert_eq!(
            parse_src("1 / 2 / 3").ast.unwrap(),
            div(div(con("1"), con("2")), con("3"))
        );
    }

    #[test]
    fn mul_div() {
        assert_eq!(
            parse_src("1 * 2 / 3").ast.unwrap(),
            div(mul(con("1"), con("2")), con("3"))
        );
    }

    #[test]
    fn div_mul() {
        assert_eq!(
            parse_src("1 / 2 * 3").ast.unwrap(),
            mul(div(con("1"), con("2")), con("3"))
        );
    }

    #[test]
    fn single_exp() {
        assert_eq!(parse_src("1 ^ 2").ast.unwrap(), exp(con("1"), con("2")));
    }

    #[test]
    fn multiple_exp() {
        assert_eq!(
            parse_src("1 ^ 2 ^ 3").ast.unwrap(),
            exp(exp(con("1"), con("2")), con("3"))
        );
    }

    #[test]
    fn parens() {
        // Without parens (multiplication before addition)
        assert_eq!(
            parse_src("1 + 2 * 3").ast.unwrap(),
            add(con("1"), mul(con("2"), con("3")))
        );
        assert_eq!(
            parse_src("1 * 2 + 3").ast.unwrap(),
            add(mul(con("1"), con("2")), con("3"))
        );

        // With parens (order is changed, addition before multiplication)
        assert_eq!(
            parse_src("(1 + 2) * 3").ast.unwrap(),
            mul(add(con("1"), con("2")), con("3"))
        );
        assert_eq!(
            parse_src("1 * (2 + 3)").ast.unwrap(),
            mul(con("1"), add(con("2"), con("3")))
        );
    }

    #[test]
    fn pemdas() {
        assert_eq!(
            parse_src("2 * 6 / (8 - 2) - 2 ^ 3 + 3 * 4").ast.unwrap(),
            add(
                sub(
                    div(mul(con("2"), con("6")), sub(con("8"), con("2"))),
                    exp(con("2"), con("3"))
                ),
                mul(con("3"), con("4"))
            )
        );
    }
}
