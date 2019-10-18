#![allow(unused_variables)]
#![allow(dead_code)]

use nom::error::VerboseError;
use std::rc::Rc;

pub type FeRet<'a> = Result<Fexp, Ferr<'a>>;

#[derive(Debug, Ord, PartialOrd, Eq, PartialEq, Clone)]
pub enum Fexp {
    FAtom(Atom),
    Func(Rc<Fexp>, Vec<Fexp>),
    Quote(Vec<Fexp>),
}

#[derive(Debug, PartialEq, Clone)]
pub enum Ferr<'a> {
    ErrTrace(VerboseError<&'a str>),
    ErrMsg(String),
}

#[derive(Debug, Ord, PartialOrd, Eq, PartialEq, Clone)]
pub enum Primitive {
    Add,
    Sub,
    Mul,
    Div,
    Eq,
    Not,
    Println,
}

#[derive(Debug, Ord, PartialOrd, Eq, PartialEq, Clone)]
pub enum Atom {
    // Literals
    String(String),
    Number(i64),

    // Primitive ops
    Op(Primitive),

    // :foo style keywords in lisp
    Kw(String),

    // Special Symbols
    Nil,
    Bool(bool),

    // Everything else that isn't reserved
    // is a "vanilla" symbol.
    Symbol(String),
}

fn escape_str(s: &str) -> String {
    s.chars()
        .map(|c| match c {
            '"' => "\\\"".to_string(),
            '\n' => "\\n".to_string(),
            '\\' => "\\\\".to_string(),
            _ => c.to_string(),
        })
        .collect::<Vec<String>>()
        .join("")
}

impl Atom {
    pub fn as_str(&self) -> String {
        match self {
            Atom::Symbol(s) => s.clone(),
            _ => unimplemented!(),
        }
    }
}

impl Fexp {
    pub fn as_str(&self) -> String {
        match self {
            Fexp::FAtom(a) => match a {
                Atom::String(s) => format!("{}", s.clone()),
                Atom::Number(n) => format!("{}", n),
                Atom::Kw(kw) => format!(":{}", &kw),
                Atom::Nil => String::from("nil"),
                Atom::Bool(true) => String::from("true"),
                Atom::Bool(false) => String::from("false"),
                Atom::Op(o) => op_to_str(o),
                Atom::Symbol(sym) => sym.clone(),
                _ => unreachable!(),
            },
            Fexp::Func(x, xs) => {
                let xs: Vec<String> = xs.iter().map(|x| x.as_str()).collect();
                format!("({} {})", x.as_str(), xs.join(" "))
            }
            Fexp::Quote(q) => {
                let qs: Vec<String> = q.iter().map(|_q| _q.as_str()).collect();
                format!("({})", qs.join(" "))
            }
        }
    }
}

fn op_to_str(o: &Primitive) -> String {
    match o {
        Primitive::Add => String::from("+"),
        Primitive::Sub => String::from("-"),
        Primitive::Mul => String::from("*"),
        Primitive::Div => String::from("/"),
        Primitive::Eq => String::from("="),
        Primitive::Not => String::from("not"),
        Primitive::Println => String::from("println"),
    }
}
