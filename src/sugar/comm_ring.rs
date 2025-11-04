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
                "expected (comm-ring <datatype> <zero> <one> <inverse> <add> <mul>)".to_string(),
            ));
        }

        let datatype = args[0].expect_atom("datatype").unwrap();
        let zero = &args[1];
        let one = &args[2];

        let inv = args[3].expect_list("inverse").unwrap();
        let inv_v = inv[0].expect_atom("inverse");
        let inv_body = &inv[1];

        let add = args[4].expect_list("inverse").unwrap();
        let add_v1 = add[0].expect_atom("add");
        let add_v2 = add[1].expect_atom("add");
        let add_body = &add[2];

        let mul = args[5].expect_list("inverse").unwrap();
        let mul_v1 = mul[0].expect_atom("mul");
        let mul_v2 = mul[1].expect_atom("mul");
        let mul_body = &mul[2];

        let cr_dt = parser.symbol_gen.fresh(&format!("cr_{datatype}_dt"));
        let cr_zero = parser.symbol_gen.fresh(&format!("cr_{datatype}_zero"));
        let cr_one = parser.symbol_gen.fresh(&format!("cr_{datatype}_one"));
        let cr_inv = parser.symbol_gen.fresh(&format!("cr_{datatype}_inv"));
        let cr_add = parser.symbol_gen.fresh(&format!("cr_{datatype}_add"));
        let cr_mul = parser.symbol_gen.fresh(&format!("cr_{datatype}_mul"));
        let cr_of_orig = parser.symbol_gen.fresh(&format!("cr_{datatype}_crof"));

        Ok(vec![
            // create datatype for CRing
            Command::Datatype {
                span: span.clone(),
                name: cr_dt.clone(),
                variants: vec![
                    Variant {
                        span: span.clone(),
                        name: cr_of_orig,
                        types: vec![datatype],
                        cost: None,
                        unextractable: true,
                    },
                    Variant {
                        span: span.clone(),
                        name: cr_zero,
                        types: vec![],
                        cost: None,
                        unextractable: true,
                    },
                    Variant {
                        span: span.clone(),
                        name: cr_one,
                        types: vec![],
                        cost: None,
                        unextractable: true,
                    },
                    Variant {
                        span: span.clone(),
                        name: cr_inv,
                        types: vec![cr_dt.clone()],
                        cost: None,
                        unextractable: true,
                    },
                    Variant {
                        span: span.clone(),
                        name: cr_add,
                        types: vec![cr_dt.clone(), cr_dt.clone()],
                        cost: None,
                        unextractable: true,
                    },
                    Variant {
                        span: span.clone(),
                        name: cr_mul,
                        types: vec![cr_dt.clone(), cr_dt.clone()],
                        cost: None,
                        unextractable: true,
                    },
                ],
            },
            // map between user-defined datatype and CRing

            // CRing axioms
        ]) // TODO: add rewrites for CRing axioms
    }
}
