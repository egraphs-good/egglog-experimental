//// TODO: Remove most of this. Dont store solver state in the egraph.
/// Instead add high level commands
///


/// should be able to do these: https://smt-lib.org/examples.shtml
//
//
// Examples:

// ; Basic Boolean example
// (set-option :print-success false)
// (set-logic QF_UF)
// (declare-const p Bool)
// (assert (and p (not p)))
// (check-sat) ; returns 'unsat'
// (exit)

// This should be in egglog:
// (let p (smt-bool-const "p"))
// (check (is-unsat "QF_UF" (and p (not p))))

// ; Integer arithmetic
// (set-logic QF_LIA)
// (declare-const x Int)
// (declare-const y Int)
// (assert (= (- x y) (+ x (- y) 1)))
// (check-sat)
// ; unsat
// (exit)

// This should be in egglog:
// (let x (smt-int-const "x"))
// (let y (smt-int-const "y"))
// (check (is-unsat "QF_LIA" (= (- x y) (+ x (- y) (smt-int 1)))))

// ; Getting values or models
// (set-option :print-success false)
// (set-option :produce-models true)
// (set-logic QF_LIA)
// (declare-const x Int)
// (declare-const y Int)
// (assert (= (+ x (* 2 y)) 20))
// (assert (= (- x y) 2))
// (check-sat)
// ; sat
// (get-value (x y))
// ; ((x 8) (y 6))
// (get-model)
// ; ((define-fun x () Int 8)
// ;  (define-fun y () Int 6)
// ; )
// (exit)

// This should be in egglog:
// (let x (smt-int-const "x"))
// (let y (smt-int-const "y"))
// (let model (smt-model "QF_LIA" (smt-= (+ x (* (smt-int 2) y)) (smt-int 20))) (smt-= (- x y) (smt-int 2)))))
// (check (= (get-value model x) (smt-int 8)))
// (check (= (get-value model y) (smt-int 6)))

/// TODO: add more examples
use core::fmt;
use egglog::add_primitive;
use egglog::sort::S;
use std::cell::RefCell;
use std::rc::Rc;
use std::sync::{LazyLock, RwLock};
use std::{
    fmt::Debug,
    hash::Hash,
    sync::{Arc, Mutex},
};

// static STORAGE: LazyLock<Mutex<smt::Storage>> = LazyLock::new(|| Mutex::new(smt::Storage::new()));
// lazy_static! {
//     static ref STORAGE: Mutex<smt::Storage> = Mutex::new(smt::Storage::new());
// }

// static storage = smt::Storage::new();

use egglog::{
    BaseValue, EGraph, Term, TermDag, Value,
    prelude::{BaseSort, RustSpan, Span, add_base_sort},
    sort::BaseValues,
    span,
};
use smtlib_lowlevel as smt;

pub fn add_smt(egraph: &mut EGraph) {
    // add_base_sort(egraph, SMTCommandSort, span!()).unwrap();
    add_base_sort(egraph, SMTBackendSort, span!()).unwrap();
}

#[derive(Clone)]
pub struct BackendValue {
    backend: Arc<smt::backend::cvc5_binary::Cvc5Binary>,
    // commands: Arc<Vec<smt::ast::Command<'static>>>,
    // outputs: Vec<smt::ast::GeneralResponse<'static>>,
}

impl Default for BackendValue {
    fn default() -> Self {
        let backend = Arc::new(smt::backend::cvc5_binary::Cvc5Binary::new("cvc5").unwrap());
        BackendValue {
            backend,
            // commands: Arc::new(vec![]),
            // outputs: vec![],
        }
    }
}

impl PartialEq for BackendValue {
    fn eq(&self, other: &Self) -> bool {
        self.backend == other.backend
    }
}

impl Hash for BackendValue {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.commands.hash(state);
    }
}

impl Eq for BackendValue {}

impl BaseValue for BackendValue {}

impl Debug for BackendValue {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        todo!("Implement Debug for DriverValue, which is used when serializing")
    }
}

#[derive(Debug)]
pub struct SMTBackendSort;

impl BaseSort for SMTBackendSort {
    type Base = BackendValue;

    fn name(&self) -> &str {
        "SMTBackend"
    }

    fn reconstruct_termdag(&self, _: &BaseValues, _: Value, _: &mut TermDag) -> Term {
        todo!()
    }

    fn register_primitives(&self, eg: &mut EGraph) {
        add_primitive!(
            eg,
            "smt-backend-new" = || -> BackendValue { BackendValue::default() }
        );
        add_primitive!(eg, "smt-backend-set-logic" =
            |mut backend: BackendValue, logic: S| -> BackendValue {{
                let storage = smt::Storage::new();
                let sym = smt::lexicon::Symbol(storage.alloc_str(&logic.to_string()));
                let cmd: smt::ast::Command<'static> = smt::ast::Command::SetLogic(sym);
                // backend.commands.push(cmd);
                backend
            }}
        );
    }
}

// implement as own enum isntead of using smt::ast::Command directly since that one takes references
// and we don't want to deal with lifetimes with values
// #[derive(Clone, PartialEq, Hash, Debug)]
// pub enum CommandValue {
//     SetLogic(String),
// }

// impl CommandValue {
//     pub fn to_ast<'a>(&'a self, storage: &'a smt::Storage) -> smt::ast::Command<'a> {
//         match self {
//             CommandValue::SetLogic(logic) => {
//                 smt::ast::Command::SetLogic(smt::lexicon::Symbol(storage.alloc_str(logic)))
//             }
//         }
//     }
// }

// impl Eq for CommandValue {}

// impl BaseValue for CommandValue {}

// #[derive(Debug)]
// pub struct SMTCommandSort;

// impl BaseSort for SMTCommandSort {
//     type Base = CommandValue;

//     fn name(&self) -> &str {
//         "SMTCommand"
//     }

//     fn reconstruct_termdag(&self, _: &BaseValues, _: Value, _: &mut TermDag) -> Term {
//         todo!()
//     }

//     fn register_primitives(&self, eg: &mut EGraph) {
//         add_primitive!(
//             eg,
//             "smt-command-set-logic" =
//                 |logic: S| -> CommandValue { CommandValue::SetLogic(logic.to_string()) }
//         );
//         // add_primitive!(eg, "smt-backend-new" = || -> BackendValue { BackendValue::default() });
//         // add_primitive!(eg, "smt-backend-exec"
//     }
// }
