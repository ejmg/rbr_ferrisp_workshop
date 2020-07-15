#![allow(unused_variables)]
#![allow(dead_code)]

use crate::lib::types::{Atom, FeRet, Ferr, Fexp, Primitive};
use std::rc::Rc;

use nom::{
    branch::alt,
    bytes::complete::{escaped, escaped_transform, is_not, tag, take_while, take_while1},
    character::complete::{char, digit1, multispace0, multispace1, one_of},
    combinator::{complete, cut, map, map_parser, map_res, recognize, value},
    error::{context, convert_error, VerboseError},
    multi::many0,
    sequence::{delimited, preceded, terminated, tuple},
    Err, IResult,
};

pub struct Parser;

impl Parser {
    pub fn parse(input: &str) -> FeRet {
        match complete(parse_fexpr)(input) {
            Ok((xs, x)) => Ok(x),
            Err(Err::Error(e)) | Err(Err::Failure(e)) => Err(Ferr::ErrTrace(e)),

            _ => unreachable!(),
        }
    }
}

fn crlf_wsc<'a>(i: &'a str) -> IResult<&'a str, &'a str, VerboseError<&'a str>> {
    let chars = " \t\r\n,";

    take_while(move |c| chars.contains(c))(i)
}

fn not_crlf_wsc<'a>(s: &'a str) -> IResult<&'a str, &'a str, VerboseError<&'a str>> {
    is_not(" \t\r\n,")(s)
}

fn not_reserved<'a>(s: &'a str) -> IResult<&'a str, &'a str, VerboseError<&'a str>> {
    is_not(" \t\r\n,^~@'`[](){}")(s)
}

fn valid_str<'a>(i: &'a str) -> IResult<&'a str, &'a str, VerboseError<&'a str>> {
    // ASCII except for control characters, `"`, and `\` itself.
    let chars = " !#$%&'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[]^_`abcdefghijklmnopqrstuvwxyz{|}";
    println!("symbol: {:#?}", i);
    take_while1(move |c| chars.contains(c))(i)
    // take_while_m_n(0, i.len() - 1, move |c| chars.contains(c))(i)
}

fn valid_symbols<'a>(i: &'a str) -> IResult<&'a str, &'a str, VerboseError<&'a str>> {
    // ASCII except for control characters, special symbols in Ferrisp, brackets,
    // `.`, and whitespace. `:` are considered legal because parsers are assumed to handle logic
    // of quoted keywords, i.e. `':foo`, which would eval to `:foo`
    let chars = "!#$%&*+-/0123456789:<=>?ABCDEFGHIJKLMNOPQRSTUVWXYZ_abcdefghijklmnopqrstuvwxyz";
    println!("valid_symbol: {:#?}", i);
    take_while1(move |c| chars.contains(c))(i)
}

fn valid_kw<'a>(i: &'a str) -> IResult<&'a str, &'a str, VerboseError<&'a str>> {
    // ASCII except for control characters, special symbols in Ferrisp, brackets,
    // `.`, and whitespace. Does NOT include `:`
    let chars = "!#$%&*+-/0123456789<=>?ABCDEFGHIJKLMNOPQRSTUVWXYZ_abcdefghijklmnopqrstuvwxyz";
    println!("valid_kw: {:#?}", i);

    take_while1(move |c| chars.contains(c))(i)
}

fn prim_numeric<'a>(i: &'a str) -> IResult<&'a str, Primitive, VerboseError<&'a str>> {
    println!("prim_numeric: {:#?}", i);
    alt((
        value(Primitive::Add, char('+')),
        value(Primitive::Sub, char('-')),
        value(Primitive::Mul, char('*')),
        value(Primitive::Div, char('/')),
        value(Primitive::Eq, char('=')),
    ))(i)
}

fn prim_fn<'a>(i: &'a str) -> IResult<&'a str, Primitive, VerboseError<&'a str>> {
    println!("prim_fn: {:#?}", i);

    alt((
        value(Primitive::Not, tag("not")),
        value(Primitive::Println, tag("println")),
    ))(i)
}

fn primitive<'a>(i: &'a str) -> IResult<&'a str, Primitive, VerboseError<&'a str>> {
    println!("primitive: {:#?}", i);
    alt((prim_numeric, prim_fn))(i)
}

fn special<'a>(i: &'a str) -> IResult<&'a str, &'a str, VerboseError<&'a str>> {
    println!("special: {:#?}", i);
    alt((tag("`"), tag("'"), tag("~")))(i)
}

// fn list<'a>(i: &'a str) -> IResult<&'a str, &'a str, VerboseError<&'a str>> {
//     delimited(tag("("), sep: G, second: H)
// }

fn bool<'a>(i: &'a str) -> IResult<&'a str, Atom, VerboseError<&'a str>> {
    println!("bool: {:#?}", i);
    alt((
        value(Atom::Bool(true), tag("true")),
        value(Atom::Bool(false), tag("false")),
    ))(i)
}

fn nil<'a>(i: &'a str) -> IResult<&'a str, Atom, VerboseError<&'a str>> {
    println!("nil: {:#?}", i);

    value(Atom::Nil, tag("nil"))(i)
}

fn truthy_nil<'a>(i: &'a str) -> IResult<&'a str, Atom, VerboseError<&'a str>> {
    println!("truthy_nil: {:#?}", i);

    terminated(alt((bool, nil)), multispace1)(i)
}

fn neg_int<'a>(i: &'a str) -> IResult<&'a str, &'a str, VerboseError<&'a str>> {
    println!("neg_int: {:#?}", i);

    preceded(tag("-"), digit1)(i)
}

fn integer<'a>(i: &'a str) -> IResult<&'a str, i64, VerboseError<&'a str>> {
    println!("integer: {:#?}", i);

    alt((
        map_res(recognize(neg_int), |s: &str| s.parse::<i64>()),
        map_res(digit1, |s: &str| s.parse::<i64>()),
    ))(i)
}

fn comment<'a>(i: &'a str) -> IResult<&'a str, &'a str, VerboseError<&'a str>> {
    println!("comment: {:#?}", i);

    preceded(take_while1(|s: char| s == ';'), is_not("\r\n"))(i)
}

// fn wsc_wrapper<'a>(i: &'a str) -> IResult<&'a str, String, VerboseError<&'a str>> {
//     map(separated_list(crlf_wsc, not_crlf_wsc), |_s: Vec<&str>| {
//         _s.concat()
//     })(i)
// }

fn esc_str<'a>(i: &'a str) -> IResult<&'a str, &'a str, VerboseError<&'a str>> {
    // For whatever reason, \n is special in that it doesn't need to be escaped whatsoever
    // for the combinator to work as inptended.
    println!("esc_str: {:#?}", i);

    escaped(valid_str, '\\', one_of(r#""n\"#))(i)
}

fn delim_esc<'a>(i: &'a str) -> IResult<&'a str, &'a str, VerboseError<&'a str>> {
    // println!("fn delim_esc: {}", i);
    println!("delim_esc: {:#?}", i);

    delimited(tag("\""), esc_str, tag("\""))(i)
}

fn trans_string<'a>(i: &'a str) -> IResult<&'a str, String, VerboseError<&'a str>> {
    // println!("fn string: {:?}", i);
    println!("trans_string: {:#?}", i);

    escaped_transform(valid_str, '\\', |s: &str| {
        alt((
            value("\\", tag("\\")),
            value("\"", tag("\"")),
            value("\n", tag("n")),
        ))(s)
    })(i)
}

fn str_lit<'a>(i: &'a str) -> IResult<&'a str, String, VerboseError<&'a str>> {
    println!("str_lit: {:#?}", i);

    alt((
        value(i.to_owned(), tag(r#""""#)),
        map_parser(delim_esc, trans_string),
    ))(i)
}

fn kw<'a>(i: &'a str) -> IResult<&'a str, String, VerboseError<&'a str>> {
    println!("kw: {:#?}", i);

    map(preceded(tag(":"), valid_kw), |s: &str| s.to_string())(i)
}

fn symbol<'a>(i: &'a str) -> IResult<&'a str, Atom, VerboseError<&'a str>> {
    println!("symbol: {:#?}", i);

    map(valid_symbols, |s| Atom::Symbol(String::from(s)))(i)
}

fn atom<'a>(i: &'a str) -> IResult<&'a str, Atom, VerboseError<&'a str>> {
    println!("atom: {:#?}", i);

    alt((
        bool,
        nil,
        map(primitive, Atom::Op),
        map(str_lit, Atom::String),
        map(kw, Atom::Kw),
        // If all else fails, we then check for symbol status
        symbol,
    ))(i)
}

fn f_atom<'a>(i: &'a str) -> IResult<&'a str, Fexp, VerboseError<&'a str>> {
    println!("f_atom: {:#?}", i);

    map(atom, Fexp::FAtom)(i)
}

// fn unquote<'a><'a>(i: &'a str) -> IResult<&'a str, Atom, VerboseError<&'a str>> {}
// fn backquote<'a>(i: &'a str) -> IResult<&'a str, Atom, VerboseError<&'a str>> {}

fn quote<'a>(i: &'a str) -> IResult<&'a str, Fexp, VerboseError<&'a str>> {
    println!("quote: {:#?}", i);
    alt((
        map(preceded(tag("'"), s_exp(many0(parse_fexpr))), |exprs| {
            Fexp::Quote(exprs)
        }),
        // TODO: need to figure out how to unwrap the parser here from capturing symbols
        // that aren't in a list.
        // Reality is that best way to do this would be to add things like context/env, but
        // not desirable for keeping overall simplicitly of solution minimal.

        // map(preceded(tag("'"), symbol), |s| {
        //     Fexp::Quote(vec![Fexp::FAtom(s)])
        // }),
        // map(preceded(tag("'"), symbol), |s| {
        //     Fexp::FAtom(Atom::Symbol(format!("'{}", s.as_str())))
        // }),
        map(preceded(tag("'"), symbol), |s| Fexp::FAtom(s)),
    ))(i)
}

fn func<'a>(i: &'a str) -> IResult<&'a str, Fexp, VerboseError<&'a str>> {
    println!("func: {:#?}", i);
    let inner_expr = map(tuple((parse_fexpr, many0(parse_fexpr))), |(x, xs)| {
        Fexp::Func(Rc::new(x), xs)
    });
    s_exp(inner_expr)(i)
}

fn parse_fexpr<'a>(i: &'a str) -> IResult<&'a str, Fexp, VerboseError<&'a str>> {
    // preceded(multispace0, alt((parse_FAtom, parse_Fn, parse_Quote)))(i)
    println!("parse_fexpr: {:#?}", i);
    preceded(multispace0, alt((f_atom, func, quote)))(i)
}

/// Before continuing, we need a helper function to parse lists.
/// A list starts with `(` and ends with a matching `)`.
/// By putting whitespace and newline parsing here, we can avoid having to worry about it
/// in much of the rest of the parser.
///
/// Unlike the previous functions, this function doesn't take or consume input, instead it
/// takes a parsing function and returns a new parsing function.
fn s_exp<'a, O1, F>(inner: F) -> impl Fn(&'a str) -> IResult<&'a str, O1, VerboseError<&'a str>>
where
    F: Fn(&'a str) -> IResult<&'a str, O1, VerboseError<&'a str>>,
{
    delimited(
        char('('),
        preceded(multispace0, inner),
        context("closing paren", cut(preceded(multispace0, char(')')))),
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use nom::error::{
        ErrorKind::{MultiSpace, Tag},
        VerboseErrorKind::Nom,
    };
    use nom::Err::Error;

    #[test]
    fn test_crlf_wsc() {
        let input = "  ,\n foo";
        let (rem, res) = crlf_wsc(input).unwrap();
        assert_eq!("  ,\n ", res);
        assert_eq!("foo", rem);
    }

    #[test]
    fn test_special() {
        let unquote = "~Foo";

        assert_eq!(special(unquote), Ok(("Foo", "~")));

        let tilde = "~123Bar";
        assert_eq!(special(tilde), Ok(("123Bar", "~")));
    }

    #[test]
    fn test_comment() {
        let comment_0 = "; Hello and welcome to my sick twisted mind \n";
        let comment_1 = ";Hello and welcome to my sick twisted mind \r\n";
        let comment_2 = ";;;; Hello and welcome to my sick twisted mind \r\n";

        assert_eq!(
            comment(comment_0),
            Ok(("\n", " Hello and welcome to my sick twisted mind "))
        );
        assert_eq!(
            comment(comment_1),
            Ok(("\r\n", "Hello and welcome to my sick twisted mind "))
        );

        assert_eq!(
            comment(comment_2),
            Ok(("\r\n", " Hello and welcome to my sick twisted mind "))
        );
    }

    #[test]
    fn test_truthy_nil() {
        let bad_but_valid_identifier_0 = "trueFudge";
        let bad_but_valid_identifier_1 = "nilQux";
        let true_ws = "true ";
        let nil_crlf = "nil\r\n";
        let false_tab = "false\t";

        assert_eq!(
            truthy_nil(bad_but_valid_identifier_0),
            Err(Error(VerboseError {
                errors: [("Fudge", Nom(MultiSpace))].to_vec()
            }))
        );
        assert_eq!(
            truthy_nil(bad_but_valid_identifier_1),
            Err(Error(VerboseError {
                errors: [("Qux", Nom(MultiSpace))].to_vec()
            }))
        );
        assert_eq!(truthy_nil(true_ws), Ok(("", Atom::Bool(true))));
        assert_eq!(truthy_nil(nil_crlf), Ok(("", Atom::Nil)));
        assert_eq!(truthy_nil(false_tab), Ok(("", Atom::Bool(false))));
    }

    #[test]
    fn test_integer() {
        let int_0 = "1234567890";
        let int_1 = "0987654321";
        let int_2 = "-1234567890";
        let int_3 = "-01234567890";

        let (rem_0, res_0) = integer(int_0).unwrap();
        assert_eq!(res_0, "1234567890".parse::<i64>().unwrap());
        let (rem_0, res_1) = integer(int_1).unwrap();
        assert_eq!(res_1, "0987654321".parse::<i64>().unwrap());
        let (rem_0, res_2) = integer(int_2).unwrap();
        assert_eq!(res_2, "-1234567890".parse::<i64>().unwrap());
        let (rem_0, res_3) = integer(int_3).unwrap();
        // tbh i am not sure this should be an error? I guess it should, but is the effort
        // worth it? probs not.
        assert_eq!(res_3, "-1234567890".parse::<i64>().unwrap());
    }

    #[test]
    fn test_string_lit() {
        // key with these tests: the first outer set of ""'s are only singly escaped because
        // these mark the outer boundery of the string. any " inside of the string then needs
        // to be doubly escaped as do all other escaped values. this is reflected by the fact
        // that our parser expects a " at each end of the string input via delimited()'s
        // behavior.
        let str_0 = r#""Hello!""#; // simple "hello"
        let str_1 = r#""\\\\""#; // string with newline, world!
        let str_2 = r#""\\""#; // string with newline, world!
        let str_3 = "\"world\\n\"";
        let str_4 = "\"world\\n\\\"\"";
        let str_5 = r#""""#;

        let str_6 = r#""wh\"at""#;

        let (rem_0, res_0) = str_lit(str_0).unwrap();
        assert_eq!("Hello!", res_0);

        let (rem_1, res_1) = str_lit(str_1).unwrap();
        assert_eq!(r"\\", res_1);

        let (rem_2, res_2) = str_lit(str_2).unwrap();
        assert_eq!(r"\", res_2);

        let (rem_3, res_3) = str_lit(str_3).unwrap();
        assert_eq!(
            r#"world
"#,
            res_3
        );

        let (rem_4, res_4) = str_lit(str_4).unwrap();
        // println!("{:?}, {:?}", rem_4, res_4);
        assert_eq!(
            r#"world
""#,
            res_4
        );

        assert_eq!(str_lit(str_5), Ok(("", r#""""#.to_string())));
        assert_eq!(str_lit(str_6), Ok(("", r#"wh"at"#.to_string())));
    }

    #[test]
    fn test_kw() {
        let kw_0 = ":foo";
        let kw_1 = ":foo123";
        let kw_2 = ":foo-bar";
        let kw_3 = ":$hello?";

        let (rem_0, res_0) = kw(kw_0).unwrap();
        assert_eq!("foo", res_0);
        assert_eq!(kw(kw_1), Ok(("", "foo123".to_string())));
        assert_eq!(kw(kw_2), Ok(("", "foo-bar".to_string())));
        assert_eq!(kw(kw_3), Ok(("", "$hello?".to_string())));
    }

    #[test]
    fn test_quote() {
        use crate::types::{
            Atom::Symbol,
            Fexp::{FAtom, Quote},
        };
        let sym_0 = "'a";
        let sym_1 = "'a-b?";
        let quote_list_0 = "'(1 2 3)";
        let quote_list_1 = "'('a '2 ':foo)";

        assert_eq!(quote(sym_0), Ok(("", FAtom(Symbol("a".to_string())))));
        assert_eq!(quote(sym_1), Ok(("", FAtom(Symbol("a-b?".to_string())))));
        assert_eq!(
            quote(quote_list_0),
            Ok((
                "",
                Quote(vec![
                    FAtom(Symbol("1".to_string())),
                    FAtom(Symbol("2".to_string())),
                    FAtom(Symbol("3".to_string()))
                ])
            ))
        );
        assert_eq!(
            quote(quote_list_1),
            Ok((
                "",
                Quote(vec![
                    FAtom(Symbol("a".to_string())),
                    FAtom(Symbol("2".to_string())),
                    FAtom(Symbol(":foo".to_string()))
                ])
            ))
        );
    }

    #[test]
    fn test_atoms() {
        use crate::lib::types::{Atom, Primitive::Add};
        let a_0 = "+";
        let a_1 = "+ 123";
        let a_2 = "true 123";
        let a_3 = ":foo";

        assert_eq!(atom(a_0), Ok(("", Atom::Op(Add))));
        assert_eq!(atom(a_1), Ok((" 123", Atom::Op(Add))));
        assert_eq!(atom(a_2), Ok((" 123", Atom::Bool(true))));
        assert_eq!(atom(a_3), Ok(("", Atom::Kw("foo".to_string()))));
    }

    #[test]
    fn test_func() {
        use crate::lib::types::{
            Atom,
            Atom::{Op, String, Symbol},
            Fexp::{FAtom, Func},
            Primitive::{Add, Div, Mul, Println, Sub},
        };

        let fn_0 = "(+ 1 2)";
        let fn_1 = "(+ 1 (* 1 1))";
        let fn_2 = "(println \"foobar\")";
        let fn_3 = "(+ 1 (- 2 (* 3 (/ 4 5))))";

        assert_eq!(
            func(fn_0),
            Ok((
                "",
                Func(
                    Rc::new(FAtom(Op(Add))),
                    vec![
                        FAtom(Symbol("1".to_string())),
                        FAtom(Symbol("2".to_string()))
                    ]
                )
            ))
        );
        assert_eq!(
            func(fn_1),
            Ok((
                "",
                Func(
                    Rc::new(FAtom(Op(Add))),
                    vec![
                        FAtom(Symbol("1".to_string())),
                        Func(
                            Rc::new(FAtom(Op(Mul))),
                            vec![
                                FAtom(Symbol("1".to_string())),
                                FAtom(Symbol("1".to_string()))
                            ]
                        )
                    ]
                )
            ))
        );

        assert_eq!(
            func(fn_2),
            Ok((
                "",
                Func(
                    Rc::new(FAtom(Op(Println))),
                    vec![FAtom(String("foobar".to_string()))]
                )
            ))
        );

        assert_eq!(
            func(fn_3),
            Ok((
                "",
                Func(
                    Rc::new(FAtom(Op(Add))),
                    vec![
                        FAtom(Symbol("1".to_string())),
                        Func(
                            Rc::new(FAtom(Op(Sub))),
                            vec![
                                FAtom(Symbol("2".to_string())),
                                Func(
                                    Rc::new(FAtom(Op(Mul))),
                                    vec![
                                        FAtom(Symbol("3".to_string())),
                                        Func(
                                            Rc::new(FAtom(Op(Div))),
                                            vec![
                                                FAtom(Symbol("4".to_string())),
                                                FAtom(Symbol("5".to_string()))
                                            ]
                                        )
                                    ]
                                )
                            ]
                        )
                    ]
                )
            ))
        );
    }
}
