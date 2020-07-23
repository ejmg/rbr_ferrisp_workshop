#![allow(unused_variables)]
#![allow(dead_code)]

use crate::types::{Atom, FeRet, Fexp};

#[derive(Debug, Ord, PartialOrd, Eq, PartialEq, Clone)]
pub struct Ast(pub Vec<Fexp>);

impl Ast {
    // Why do we return a FeRet? Ostensibly because a quoted Fexp can't actuall see evaluation!
    // So what does that mean for evaluation? Treat a Quote => Atom.
    pub fn eval<'a>(ast: Fexp) -> FeRet<'a> {
        match ast.clone() {
            Fexp::FAtom(_) => Ok(ast),
            _ => unimplemented!(),
        }
    }
}

fn walk_ast<'a>(ast: &Fexp) -> FeRet<'a> {
    unimplemented!()
}
