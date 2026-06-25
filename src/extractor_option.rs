use egglog::{
    Error,
    ast::{Expr, ParseError},
};

pub(crate) fn parse_extractor_keyword(keyword: &Expr, extractor: &Expr) -> Result<bool, Error> {
    match keyword {
        Expr::Var(_, keyword) if keyword == ":extractor" => parse_use_greedy_dag(extractor),
        _ => Err(Error::ParseError(ParseError(
            keyword.span(),
            "expected :extractor".into(),
        ))),
    }
}

pub(crate) fn split_trailing_extractor(args: &[Expr]) -> Result<(&[Expr], bool), Error> {
    let Some(idx) = args
        .iter()
        .position(|arg| matches!(arg, Expr::Var(_, keyword) if keyword == ":extractor"))
    else {
        return Ok((args, false));
    };

    if idx + 2 != args.len() {
        return Err(Error::ParseError(ParseError(
            args[idx].span(),
            "expected trailing :extractor <name>".into(),
        )));
    }

    Ok((&args[..idx], parse_use_greedy_dag(&args[idx + 1])?))
}

fn parse_use_greedy_dag(arg: &Expr) -> Result<bool, Error> {
    match arg {
        Expr::Var(_, name) if name == "greedy-dag" => Ok(true),
        Expr::Var(_, name) => Err(Error::ParseError(ParseError(
            arg.span(),
            format!("unknown extractor: {name}; omit :extractor to use the default tree extractor"),
        ))),
        _ => Err(Error::ParseError(ParseError(
            arg.span(),
            "extractor name must be a symbol".into(),
        ))),
    }
}
