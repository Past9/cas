pub mod ast;
pub mod simplify;

use std::str::FromStr;

use chumsky::{
    primitive::{end, just},
    recursive::recursive,
    select, Parser, Stream,
};
use rust_decimal::Decimal;

use crate::{
    error::SyntaxError,
    tokenize::{tokenize_src, tokens::Token},
    Spanned,
};

use self::ast::{ast_helpers::*, Ast};

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
        let keywords = select! {
            Token::Undefined => Ast::Und,
        }
        .boxed();

        let symbol = select! {
            Token::Ident(name) => sym(&name),
        }
        .boxed();

        let constant = select! {
            Token::Const(text) => {
                let dec = Decimal::from_str(&text).expect(&format!("Could not parse {} as number", text));
                Ast::from_dec(dec)
            }
        }
        .boxed();

        let comma_list = expr
            .clone()
            .separated_by(just(Token::Comma))
            .allow_trailing()
            .boxed();

        let function = select! {
            Token::Ident(name) => name
        }.then(comma_list.delimited_by(just(Token::OpenParen), just(Token::CloseParen)))
        .map(|(name, args)| {
            Ast::Fun(name.to_owned(), args.to_vec())
        })
        .boxed();


        let atom = keywords
            .or(function)
            .or(symbol)
            .or(constant)
            .or(expr
                .clone()
                .delimited_by(just(Token::OpenParen), just(Token::CloseParen)))
            .boxed();


        let factorial = atom
            .then(just(Token::Bang).repeated())
            .foldl(|operand, _op| fac(operand))
            .boxed();

        let neg = just(Token::Minus)
            .repeated()
            .then(factorial)
            .foldr(|_op, operand| neg(operand))
            .boxed();

        let exp = neg
            .clone()
            .then(just(Token::Caret).then(neg).repeated())
            .foldl(|left, (_op, right)| pow(left, right))
            .boxed();


        let mul_div = exp
            .clone()
            .then(
                just(Token::Asterisk)
                    .or(just(Token::FwdSlash))
                    .then(exp)
                    .repeated(),
            )
            .foldl(|left, (op, right)|  {
                if op == Token::Asterisk {
                    prd([left, right])
                } else if op == Token::FwdSlash {
                    quo(left, right)
                } else {
                    panic!("Invalid operator at mul/div precedence level: {:?}", op)
                }
            })
            .boxed();

        let add_sub = mul_div
            .clone()
            .then(
                just(Token::Plus)
                    .or(just(Token::Minus))
                    .then(mul_div)
                    .repeated(),
            )
            .foldl(|left, (op, right)| {
                if op == Token::Plus {
                    sum([left, right])
                } else if op == Token::Minus {
                    dif(left, right)
                } else {
                    panic!("Invalid operator at add/sub precedence level: {:?}", op)
                }
            })
            .boxed();

        add_sub
    })
    .then_ignore(end())
}

#[cfg(test)]
mod tests {
    use crate::parse::ast::ast_helpers::{dif, fac, frc, int, neg, pow, prd, quo, sum, sym, und};

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
        assert_eq!(parse_src("3!").ast.unwrap(), fac(int(3)));
    }

    #[test]
    fn double_factorial() {
        assert_eq!(parse_src("3!!").ast.unwrap(), fac(fac(int(3))));
    }

    #[test]
    fn neg_factorial() {
        assert_eq!(parse_src("-3!").ast.unwrap(), neg(fac(int(3))));
    }

    #[test]
    fn pos_integer() {
        assert_eq!(parse_src("123").ast.unwrap(), int(123));
    }

    #[test]
    fn neg_integer() {
        assert_eq!(parse_src("-123").ast.unwrap(), neg(int(123)));
    }

    #[test]
    fn pos_decimal() {
        assert_eq!(parse_src("123.456").ast.unwrap(), frc(123456, 1000));
    }

    #[test]
    fn neg_decimal() {
        assert_eq!(parse_src("-123.456").ast.unwrap(), neg(frc(123456, 1000)));
    }

    #[test]
    fn single_add() {
        assert_eq!(parse_src("1 + 2").ast.unwrap(), sum([int(1), int(2)]));
    }

    #[test]
    fn multiple_add() {
        assert_eq!(
            parse_src("1 + 2 + 3").ast.unwrap(),
            sum([sum([int(1), int(2)]), int(3)])
        );
    }

    #[test]
    fn single_sub() {
        assert_eq!(parse_src("1 - 2").ast.unwrap(), dif(int(1), int(2)));
    }

    #[test]
    fn multiple_sub() {
        assert_eq!(
            parse_src("1 - 2 - 3").ast.unwrap(),
            dif(dif(int(1), int(2)), int(3))
        );
    }

    #[test]
    fn add_sub() {
        assert_eq!(
            parse_src("1 + 2 - 3").ast.unwrap(),
            dif(sum([int(1), int(2)]), int(3))
        );
    }

    #[test]
    fn sub_add() {
        assert_eq!(
            parse_src("1 - 2 + 3").ast.unwrap(),
            sum([dif(int(1), int(2)), int(3)])
        );
    }

    #[test]
    fn add_sub_ltr() {
        // Ensures addition and subtration are parsed left-to-right at the same precedence
        // instead of prioritizing one over the other, which can give incorrect/unexpected results.
        assert_eq!(
            parse_src("2 + 3 - 4 + 5").ast.unwrap(),
            sum([dif(sum([int(2), int(3)]), int(4)), int(5)])
        );
        assert_eq!(
            parse_src("2 - 3 + 4 - 5").ast.unwrap(),
            dif(sum([dif(int(2), int(3)), int(4)]), int(5))
        );
    }

    #[test]
    fn single_mul() {
        assert_eq!(parse_src("1 * 2").ast.unwrap(), prd([int(1), int(2)]));
    }

    #[test]
    fn multiple_mul() {
        assert_eq!(
            parse_src("1 * 2 * 3").ast.unwrap(),
            prd([prd([int(1), int(2)]), int(3)])
        );
    }

    #[test]
    fn single_div() {
        assert_eq!(parse_src("1 / 2").ast.unwrap(), quo(int(1), int(2)));
    }

    #[test]
    fn multiple_div() {
        assert_eq!(
            parse_src("1 / 2 / 3").ast.unwrap(),
            quo(quo(int(1), int(2)), int(3))
        );
    }

    #[test]
    fn mul_div() {
        assert_eq!(
            parse_src("1 * 2 / 3").ast.unwrap(),
            quo(prd([int(1), int(2)]), int(3))
        );
    }

    #[test]
    fn div_mul() {
        assert_eq!(
            parse_src("1 / 2 * 3").ast.unwrap(),
            prd([quo(int(1), int(2)), int(3)])
        );
    }

    #[test]
    fn div_mul_ltr() {
        // Ensures multiplication and division are parsed left-to-right at the same precedence
        // instead of prioritizing one over the other, which can give incorrect/unexpected results.
        assert_eq!(
            parse_src("2 * 3 / 4 * 5").ast.unwrap(),
            prd([quo(prd([int(2), int(3)]), int(4)), int(5)])
        );
        assert_eq!(
            parse_src("2 / 3 * 4 / 5").ast.unwrap(),
            quo(prd([quo(int(2), int(3)), int(4)]), int(5))
        );
    }

    #[test]
    fn single_exp() {
        assert_eq!(parse_src("1 ^ 2").ast.unwrap(), pow(int(1), int(2)));
    }

    #[test]
    fn multiple_exp() {
        assert_eq!(
            parse_src("1 ^ 2 ^ 3").ast.unwrap(),
            pow(pow(int(1), int(2)), int(3))
        );
    }

    #[test]
    fn parens() {
        // Without parens (multiplication before addition)
        assert_eq!(
            parse_src("1 + 2 * 3").ast.unwrap(),
            sum([int(1), prd([int(2), int(3)])])
        );
        assert_eq!(
            parse_src("1 * 2 + 3").ast.unwrap(),
            sum([prd([int(1), int(2)]), int(3)])
        );

        // With parens (order is changed, addition before multiplication)
        assert_eq!(
            parse_src("(1 + 2) * 3").ast.unwrap(),
            prd([sum([int(1), int(2)]), int(3)])
        );
        assert_eq!(
            parse_src("1 * (2 + 3)").ast.unwrap(),
            prd([int(1), sum([int(2), int(3)])])
        );
    }

    #[test]
    fn pemdas() {
        assert_eq!(
            parse_src("2 * 6 / (8 - 2) - 2 ^ 3 + 3 * 4").ast.unwrap(),
            sum([
                dif(
                    quo(prd([int(2), int(6)]), dif(int(8), int(2))),
                    pow(int(2), int(3))
                ),
                prd([int(3), int(4)])
            ])
        );
    }

    #[test]
    fn undefined() {
        assert_eq!(
            parse_src("undefined + x").ast.unwrap(),
            sum([und(), sym("x")])
        )
    }

    #[test]
    fn function() {
        assert_eq!(parse_src("f(x)").ast.unwrap(), fun("f", [sym("x")]));
        assert_eq!(
            parse_src("f(x, y)").ast.unwrap(),
            fun("f", [sym("x"), sym("y")])
        );
        assert_eq!(
            parse_src("f(x, g(y))").ast.unwrap(),
            fun("f", [sym("x"), fun("g", [sym("y")])])
        );
    }
}
