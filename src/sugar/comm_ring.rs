use egglog::{ast::*, util::FreshGen};
use egglog_ast::span::Span;

pub struct CommRing;

impl Macro<Vec<Command>> for CommRing {
    fn name(&self) -> &str {
        "comm-ring"
    }

    fn parse(
        &self,
        args: &[Sexp],
        span: Span,
        parser: &mut Parser,
    ) -> Result<Vec<Command>, ParseError> {
        if args.len() != 6 {
            return Err(ParseError(
                span,
                "expected (comm-ring <ruleset> <datatype> <zero> <one> <inverse> <add> <mul>)"
                    .to_string(),
            ));
        }

        let ruleset = args[0].expect_atom("ruleset").unwrap();
        let datatype = args[1].expect_atom("datatype").unwrap();
        let zero = &args[2];
        let one = &args[3];

        let inv = args[4].expect_list("inverse").unwrap();
        let inv_v = inv[0].expect_atom("inverse").unwrap();
        let inv_body = &inv[1];

        let add = args[5].expect_list("inverse").unwrap();
        let add_v1 = add[0].expect_atom("add").unwrap();
        let add_v2 = add[1].expect_atom("add").unwrap();
        let add_body = &add[2];

        let mul = args[6].expect_list("inverse").unwrap();
        let mul_v1 = mul[0].expect_atom("mul").unwrap();
        let mul_v2 = mul[1].expect_atom("mul").unwrap();
        let mul_body = &mul[2];

        let cr_dt = parser.symbol_gen.fresh(&format!("cr_{datatype}_dt"));
        let cr_zero = parser.symbol_gen.fresh(&format!("cr_{datatype}_zero"));
        let cr_one = parser.symbol_gen.fresh(&format!("cr_{datatype}_one"));
        let cr_inv = parser.symbol_gen.fresh(&format!("cr_{datatype}_inv"));
        let cr_add = parser.symbol_gen.fresh(&format!("cr_{datatype}_add"));
        let cr_mul = parser.symbol_gen.fresh(&format!("cr_{datatype}_mul"));
        let cr_of_orig = parser.symbol_gen.fresh(&format!("cr_{datatype}_crof"));
        let cr_var = parser.symbol_gen.fresh("cr_var");

        Ok(vec![
            // create datatype for CRing
            Command::Datatype {
                span: span.clone(),
                name: cr_dt.clone(),
                variants: vec![
                    Variant {
                        span: span.clone(),
                        name: cr_of_orig.clone(),
                        types: vec![datatype],
                        cost: None,
                        unextractable: true,
                    },
                    Variant {
                        span: span.clone(),
                        name: cr_zero.clone(),
                        types: vec![],
                        cost: None,
                        unextractable: true,
                    },
                    Variant {
                        span: span.clone(),
                        name: cr_one.clone(),
                        types: vec![],
                        cost: None,
                        unextractable: true,
                    },
                    Variant {
                        span: span.clone(),
                        name: cr_inv.clone(),
                        types: vec![cr_dt.clone()],
                        cost: None,
                        unextractable: true,
                    },
                    Variant {
                        span: span.clone(),
                        name: cr_add.clone(),
                        types: vec![cr_dt.clone(), cr_dt.clone()],
                        cost: None,
                        unextractable: true,
                    },
                    Variant {
                        span: span.clone(),
                        name: cr_mul.clone(),
                        types: vec![cr_dt.clone(), cr_dt.clone()],
                        cost: None,
                        unextractable: true,
                    },
                ],
            },
            // map between user-defined datatype and CRing
            Command::BiRewrite(
                ruleset.clone(),
                Rewrite {
                    span: span.clone(),
                    lhs: GenericExpr::Call(
                        span.clone(),
                        cr_of_orig.clone(),
                        vec![GenericExpr::Var(span.clone(), cr_var.clone())],
                    ),
                    rhs: GenericExpr::Var(span.clone(), cr_var.clone()),
                    conditions: vec![],
                },
            ),
            Command::BiRewrite(
                ruleset.clone(),
                Rewrite {
                    span: span.clone(),
                    lhs: GenericExpr::Call(span.clone(), cr_zero.clone(), vec![]),
                    rhs: parser.parse_expr(zero).unwrap(),
                    conditions: vec![],
                },
            ),
            Command::BiRewrite(
                ruleset.clone(),
                Rewrite {
                    span: span.clone(),
                    lhs: GenericExpr::Call(span.clone(), cr_one.clone(), vec![]),
                    rhs: parser.parse_expr(one).unwrap(),
                    conditions: vec![],
                },
            ),
            Command::BiRewrite(
                ruleset.clone(),
                Rewrite {
                    span: span.clone(),
                    lhs: GenericExpr::Call(
                        span.clone(),
                        cr_inv.clone(),
                        vec![GenericExpr::Var(span.clone(), inv_v)],
                    ),
                    rhs: parser.parse_expr(inv_body).unwrap(),
                    conditions: vec![],
                },
            ),
            Command::BiRewrite(
                ruleset.clone(),
                Rewrite {
                    span: span.clone(),
                    lhs: GenericExpr::Call(
                        span.clone(),
                        cr_add.clone(),
                        vec![
                            GenericExpr::Var(span.clone(), add_v1.clone()),
                            GenericExpr::Var(span.clone(), add_v2.clone()),
                        ],
                    ),
                    rhs: parser.parse_expr(add_body).unwrap(),
                    conditions: vec![],
                },
            ),
            Command::BiRewrite(
                ruleset.clone(),
                Rewrite {
                    span: span.clone(),
                    lhs: GenericExpr::Call(
                        span.clone(),
                        cr_mul.clone(),
                        vec![
                            GenericExpr::Var(span.clone(), mul_v1.clone()),
                            GenericExpr::Var(span.clone(), mul_v2.clone()),
                        ],
                    ),
                    rhs: parser.parse_expr(mul_body).unwrap(),
                    conditions: vec![],
                },
            ),
            // CRing axioms
        ]) // TODO: add rewrites for CRing axioms
    }
}
