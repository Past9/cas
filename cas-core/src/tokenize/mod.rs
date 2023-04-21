pub mod tokens;

use chumsky::{
    primitive::{choice, end, just},
    recovery::skip_then_retry_until,
    text::{self, TextParser},
    Parser,
};

use crate::{error::SyntaxError, Spanned};

use self::tokens::Token::{self, *};

#[derive(Debug)]
pub struct TokenizerResult {
    pub tokens: Vec<Spanned<Token>>,
    pub errors: Vec<SyntaxError<char>>,
}

pub fn tokenize_src(src: &str) -> TokenizerResult {
    let (tokens, errors) = tokenizer().parse_recovery(src);
    TokenizerResult {
        tokens: match tokens {
            Some(tokens) => tokens,
            None => vec![],
        },
        errors,
    }
}

fn tokenizer() -> impl Parser<char, Vec<Spanned<Token>>, Error = SyntaxError<char>> {
    choice::<_, SyntaxError<char>>((
        // Operators
        choice((
            just('+').to(Plus),
            just('-').to(Minus),
            just('*').to(Asterisk),
            just('/').to(FwdSlash),
            just('^').to(Caret),
            just('!').to(Bang),
        )),
        // Parens
        choice((just('(').to(OpenParen), just(')').to(CloseParen))),
        text::ident().map(Ident),
        choice((
            // Number literal
            text::digits(10)
                .then_ignore(just('.'))
                .then(text::digits(10))
                .map(|(before, after)| Const(format!("{}.{}", before, after))),
            text::digits(10).map(Const),
        )),
    ))
    .recover_with(skip_then_retry_until([]))
    .map_with_span(|token, span| Spanned { inner: token, span })
    .padded()
    .repeated()
    .then_ignore(end())
    .boxed()
}
