//! # Types
//!
//! This module contains the types that make up the basis for our Ferrisp style lisp.
use nom::error::VerboseError;
use std::rc::Rc;

/// *Fer*-risp *Res*-ult *T*-ype
/// A type alias for the results of the Ferrisp [`Parser`](../parser/struct.Parser.html).
///
/// Trust me, I'm not happy about the name, either.
pub type FeRet<'a> = Result<Fexp, Ferr<'a>>;

/// The expression types of Ferrisp.
#[derive(Debug, Ord, PartialOrd, Eq, PartialEq, Clone)]
pub enum Fexp {
    /// An atom value
    FAtom(Atom),
    /// A function value, which can be _applied_
    Func(Rc<Fexp>, Vec<Fexp>),
    /// A quoted value, which
    Quote(Vec<Fexp>),
}

/// A Ferrisp error type
#[derive(Debug, PartialEq, Clone)]
pub enum Ferr<'a> {
    ErrTrace(VerboseError<&'a str>),
    ErrMsg(String),
}

/// Primitive functions built into Ferrisp
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

/// Atomic values in Ferrisp.
#[derive(Debug, Ord, PartialOrd, Eq, PartialEq, Clone)]
pub enum Atom {
    /// Literals
    String(String),
    /// Basic numeric types, 64-bit signed integers
    Number(i64),

    /// Primitive ops
    Op(Primitive),

    /// :foo style keywords in lisp
    Kw(String),

    // Special Symbols
    /// Nil
    Nil,
    /// Boolean types
    Bool(bool),

    /// Symbols
    /// Everything else that isn't reserved is a "vanilla" symbol.
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
    /// Converts a Ferrisp Expression into a Stringly value for representation.
    pub fn as_str(&self) -> String {
        match self {
            Fexp::FAtom(a) => match a {
                Atom::String(s) => {
                    if s == r#""""# {
                        r#""""#.to_string()
                    } else {
                        format!("\"{}\"", s.clone())
                    }
                }
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
