//! # Parser
//!
//! This is the meat of the the application. A set of parser combinators are defined to parse valid
//! input strings into their equivalent [`Fexp`](../types/enum.Fexp.html) representation. By the
//! time the [`Parser`](../parser/struct.Parser.html) has finished, the resulting
//! [`Fexp`](../types/enum.Fexp.html) effectively represents an AST for program evaluation. No further
//! tranformations are necessary!
//!
//! The entry point for this module begins at the [`parse`](struct.Parser.html#method.parse), which
//! just wraps around the top-level parser combinator [`parse_fexp()`](fn.parse_fexpr.html).
use crate::lib::types::{Atom, FeRet, Ferr, Fexp, Primitive};
use std::rc::Rc;

use nom::{
    branch::alt,
    bytes::complete::{escaped, escaped_transform, is_not, tag, take_while, take_while1},
    character::complete::{char, digit1, multispace0, one_of},
    combinator::{complete, cut, map, map_res, recognize, value},
    error::{context, VerboseError},
    multi::many0,
    sequence::{delimited, preceded, tuple},
    Err, IResult,
};

/// Newtype declaration for our Parser.
///
/// Nom handles all data in-memory so declaring this struct explicitly is not necessary but is
/// used to expose an API.
pub struct Parser;

impl Parser {
    /// Parses a string of input into a [`FeRet`](../types/type.FeRet.html)
    pub fn parse(input: &str) -> FeRet {
        match complete(parse_fexpr)(input) {
            Ok((xs, x)) => Ok(x),
            Err(Err::Error(e)) | Err(Err::Failure(e)) => Err(Ferr::ErrTrace(e)),
            _ => unreachable!(),
        }
    }
}

/// captures whitespace characters, `\n`, `\r`, `\t`, normal whitespace, and `,`
#[deprecated]
fn crlf_wsc<'a>(i: &'a str) -> IResult<&'a str, &'a str, VerboseError<&'a str>> {
    let chars = " \t\r\n,";

    take_while(move |c| chars.contains(c))(i)
}

/// captures all symbols that are not a reserved symbol or ws
#[deprecated]
fn not_reserved<'a>(s: &'a str) -> IResult<&'a str, &'a str, VerboseError<&'a str>> {
    is_not(" \t\r\n,^~@'`[](){}")(s)
}

/// Captures the internal content of a valid string. This is just a subset of ascii excluding
/// control characters.
fn valid_str<'a>(i: &'a str) -> IResult<&'a str, &'a str, VerboseError<&'a str>> {
    // ASCII except for control characters, `"`, and `\` itself.
    let chars = " !#$%&'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[]^_`abcdefghijklmnopqrstuvwxyz{|}";
    info!("symbol: {:#?}", i);
    take_while1(move |c| chars.contains(c))(i)
    // take_while_m_n(0, i.len() - 1, move |c| chars.contains(c))(i)
}

/// Captures the content of a valid symbol. This is just a subset of ascii excluding
/// control characters and reserved symbols.
fn valid_symbols<'a>(i: &'a str) -> IResult<&'a str, &'a str, VerboseError<&'a str>> {
    // ASCII except for control characters, special symbols in Ferrisp, brackets,
    // `.`, and whitespace. `:` are considered legal because parsers are assumed to handle logic
    // of quoted keywords, i.e. `':foo`, which would eval to `:foo`
    let chars = "!#$%&*+-/0123456789:<=>?ABCDEFGHIJKLMNOPQRSTUVWXYZ_abcdefghijklmnopqrstuvwxyz";
    info!("valid_symbol: {:#?}", i);
    take_while1(move |c| chars.contains(c))(i)
}

/// Captures the content of a valid keyword. Like a [`valid_symbols()`], except prefixed with `:`.
///
/// [`valid_symbols()`]: fn.valid_symbols.html
fn valid_kw<'a>(i: &'a str) -> IResult<&'a str, &'a str, VerboseError<&'a str>> {
    // ASCII except for control characters, special symbols in Ferrisp, brackets,
    // `.`, and whitespace. Does NOT include `:`
    let chars = "!#$%&*+-/0123456789<=>?ABCDEFGHIJKLMNOPQRSTUVWXYZ_abcdefghijklmnopqrstuvwxyz";
    info!("valid_kw: {:#?}", i);

    take_while1(move |c| chars.contains(c))(i)
}

/// Captures the [primitive _numeric_ functions](../types/enum.Primitive.html) built into Ferrisp,
/// i.e. `+`, `-`, `*`, and `/`
fn prim_numeric<'a>(i: &'a str) -> IResult<&'a str, Primitive, VerboseError<&'a str>> {
    info!("prim_numeric: {:#?}", i);
    alt((
        value(Primitive::Add, char('+')),
        value(Primitive::Sub, char('-')),
        value(Primitive::Mul, char('*')),
        value(Primitive::Div, char('/')),
    ))(i)
}

/// Captures the non-numeric [primitive functions](../types/enum.Primitive.html) built into Ferrisp,
/// i.e. the logical operators `=` and `not`, and `println`
fn prim_fn<'a>(i: &'a str) -> IResult<&'a str, Primitive, VerboseError<&'a str>> {
    info!("prim_fn: {:#?}", i);

    alt((
        value(Primitive::Not, tag("not")),
        value(Primitive::Eq, char('=')),
        value(Primitive::Println, tag("println")),
    ))(i)
}

/// Top level [`Primitive`](../types/enum.Primitive.html) combinator. See also [`prim_numeric()`]
/// and [`prim_fn()`].
///
/// [`prim_numeric()`]: fn.prim_numeric.html
/// [`prim_fn()`]: fn.prim_fn.html
fn primitive<'a>(i: &'a str) -> IResult<&'a str, Primitive, VerboseError<&'a str>> {
    info!("primitive: {:#?}", i);
    alt((prim_numeric, prim_fn))(i)
}

/// Captures boolean types and returns an [`Atom`](../types/enum.Atom.html) with their value.
fn bool<'a>(i: &'a str) -> IResult<&'a str, Atom, VerboseError<&'a str>> {
    info!("bool: {:#?}", i);
    alt((
        value(Atom::Bool(true), tag("true")),
        value(Atom::Bool(false), tag("false")),
    ))(i)
}

/// Captures nil type and returns an [`Atom`](../types/enum.Atom.html) with their value.
fn nil<'a>(i: &'a str) -> IResult<&'a str, Atom, VerboseError<&'a str>> {
    info!("nil: {:#?}", i);

    value(Atom::Nil, tag("nil"))(i)
}

/// Parses and captures a negative integer value.
fn neg_int<'a>(i: &'a str) -> IResult<&'a str, &'a str, VerboseError<&'a str>> {
    info!("neg_int: {:#?}", i);

    preceded(tag("-"), digit1)(i)
}

/// Parses and captures an integer value and returns an `i64` value.
fn integer<'a>(i: &'a str) -> IResult<&'a str, i64, VerboseError<&'a str>> {
    info!("integer: {:#?}", i);

    alt((
        map_res(recognize(neg_int), |s: &str| s.parse::<i64>()),
        map_res(digit1, |s: &str| s.parse::<i64>()),
    ))(i)
}

/// Parser combinator for capturing an [`Atom::Number`](../types/enum.Atom.html).
fn number<'a>(i: &'a str) -> IResult<&'a str, Atom, VerboseError<&'a str>> {
    map(integer, Atom::Number)(i)
}

/// Captures a Ferrisp comment, text of any length following a `;` until a newline, and returns
/// a [`Fexp`](../types/enum.Fexp.html).
///
/// Note: This is a good example of workaround. Integrating a custom `Comment` variant of
/// [`Atom`](../types/enum.Atom.html) may very well be better off here.
fn comment<'a>(i: &'a str) -> IResult<&'a str, Fexp, VerboseError<&'a str>> {
    info!("comment: {:#?}", i);

    map(
        preceded(take_while1(|s: char| s == ';'), is_not("\r\n")),
        |_| Fexp::FAtom(Atom::String("".to_string())),
    )(i)
}

/// Combinator that wraps string input to handle known escape sequences.
///
/// This allows the parser to "see" into the captured string literal in order to find its complete
/// value *or* to detect an deformed string literal with invalid escape values.
fn esc_str<'a>(i: &'a str) -> IResult<&'a str, &'a str, VerboseError<&'a str>> {
    info!("esc_str: {:#?}", i);

    escaped(valid_str, '\\', one_of(r#""n\"#))(i)
}

/// Combinator that wraps string input to handle the inner value, i.e. all characters inside the
/// first set of outer `""`.
fn delim_esc<'a>(i: &'a str) -> IResult<&'a str, &'a str, VerboseError<&'a str>> {
    // info!("fn delim_esc: {}", i);
    info!("delim_esc: {:#?}", i);

    delimited(tag("\""), esc_str, tag("\""))(i)
    // delimited(tag("\""), valid_str, tag("\""))(i)
}

/// Transforms a parsed string literal with escape values for internal representation. *Currently
/// not used*.
///
/// This is for later implementation issues, such as the string representation of a literal versus
/// its representation as a value to a function such as [`println`](../types/enum.Primitive.html)
/// e.g. if the following were a standard REPL:
/// ```
/// > "wu tang"
/// "wu tang"
/// > (println "wu tang")
/// wu tang
/// > "is\nforever"
/// "is\nforever"
/// > (println "is\nforever")
/// is
/// forever
/// ````
fn trans_string<'a>(i: &'a str) -> IResult<&'a str, String, VerboseError<&'a str>> {
    // info!("fn string: {:?}", i);
    info!("trans_string: {:#?}", i);

    escaped_transform(valid_str, '\\', |s: &str| {
        info!("we made it");
        alt((
            value("\\", tag("\\")),
            value("\"", tag("\"")),
            value("\n", tag("n")),
        ))(s)
    })(i)
}

/// Parser combinator for capturing an [Atom::String](../types/enum.Atom.html), i.e. string
/// literals.
fn str_lit<'a>(i: &'a str) -> IResult<&'a str, String, VerboseError<&'a str>> {
    info!("str_lit: {:#?}", i);

    alt((
        map(delim_esc, String::from), // map_parser(delim_esc, trans_string),
        map(tuple((tag(r#"""#), tag(r#"""#))), |_| r#""""#.to_string()), // value(i.to_owned(), tag(r#""""#)),
    ))(i)
}

/// Parser combinator for capturing an [Atom::Kw](../types/enum.Atom.html).
fn kw<'a>(i: &'a str) -> IResult<&'a str, String, VerboseError<&'a str>> {
    info!("kw: {:#?}", i);

    map(preceded(tag(":"), valid_kw), |s: &str| s.to_string())(i)
}

/// Parser combinator for capturing an [Atom::Symbol](../types/enum.Atom.html).
fn symbol<'a>(i: &'a str) -> IResult<&'a str, Atom, VerboseError<&'a str>> {
    info!("symbol: {:#?}", i);

    map(valid_symbols, |s| Atom::Symbol(String::from(s)))(i)
}

/// Top level [`Atom`](../types/enum.Atom.html) parser combinator.
fn atom<'a>(i: &'a str) -> IResult<&'a str, Atom, VerboseError<&'a str>> {
    info!("atom: {:#?}", i);

    alt((
        bool,
        nil,
        map(primitive, Atom::Op),
        number,
        map(str_lit, Atom::String),
        map(kw, Atom::Kw),
        // If all else fails, we then check for symbol status
        symbol,
    ))(i)
}

/// Parser combinator that transforms captured [`Atom`] values and maps them into their equivalent
/// [`Fexp`] type.
///
/// [`Atom`]: ../types/enum.Atom.html
/// [`Fexp`]: ../types/enum.Fexp.html
fn f_atom<'a>(i: &'a str) -> IResult<&'a str, Fexp, VerboseError<&'a str>> {
    info!("f_atom: {:#?}", i);

    map(atom, Fexp::FAtom)(i)
}

/// Top level parser combinator for capturing a [`Fexp::Quote`](../types/enum.Fexp.html).
///
/// A special combinator is needed for quoted values for the handling of one of modern lisp's most
/// famous features: its macro system.
fn quote<'a>(i: &'a str) -> IResult<&'a str, Fexp, VerboseError<&'a str>> {
    info!("quote: {:#?}", i);
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
        map(preceded(tag("'"), symbol), Fexp::FAtom),
    ))(i)
}

/// Top level parser combinator for capturing [`Fexp::Func`](../types/enum.Fexp.html).
///
/// It is worth noting that `func()` is kicks off a recursive chain call for handling `Fexp` values
/// that are possibly nested between normal function applications and quoted values.
fn func<'a>(i: &'a str) -> IResult<&'a str, Fexp, VerboseError<&'a str>> {
    info!("func: {:#?}", i);
    let inner_expr = map(tuple((parse_fexpr, many0(parse_fexpr))), |(x, xs)| {
        Fexp::Func(Rc::new(x), xs)
    });
    s_exp(inner_expr)(i)
}

/// The top level parser combinator for the Ferrisp parser. This function takes in a string input
/// and will return a [`Fexp`](../types/enum.Fexp.html).
///
/// `parse_fexpr()` checks the input for unyieldly whitespace padding and then applies the parser
/// combinator for each major type of Ferrisp values.
fn parse_fexpr<'a>(i: &'a str) -> IResult<&'a str, Fexp, VerboseError<&'a str>> {
    // preceded(multispace0, alt((parse_FAtom, parse_Fn, parse_Quote)))(i)
    info!("parse_fexpr: {:#?}", i);
    preceded(multispace0, alt((comment, f_atom, func, quote)))(i)
}

/// A higher-ordered function that handles S-expressions.
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
            Ok((
                "\n",
                Fexp::FAtom(Atom::String(
                    "".to_string() // " Hello and welcome to my sick twisted mind ".to_string()
                ))
            ))
        );
        assert_eq!(
            comment(comment_1),
            Ok((
                "\r\n",
                Fexp::FAtom(Atom::String(
                    "".to_string() //"Hello and welcome to my sick twisted mind ".to_string()
                ))
            ))
        );

        assert_eq!(
            comment(comment_2),
            Ok((
                "\r\n",
                Fexp::FAtom(Atom::String(
                    "".to_string() //" Hello and welcome to my sick twisted mind ".to_string()
                ))
            ))
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
        use crate::lib::types::{
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
