use nom::{
    branch::alt,
    bytes::complete::{escaped, escaped_transform, is_not, tag, take_while, take_while1},
    character::complete::{digit1, multispace1, one_of},
    combinator::{map, map_parser, map_res, recognize, value},
    sequence::{delimited, preceded, terminated},
    IResult,
};

fn valid_str<'a>(i: &'a str) -> IResult<&'a str, &'a str> {
    // ASCII except for control characters, `"`, and `\` itself.
    let chars = " !#$%&'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[]^_`abcdefghijklmnopqrstuvwxyz{|}";

    take_while1(move |c| chars.contains(c))(i)
}

fn valid_symbols<'a>(i: &'a str) -> IResult<&'a str, &'a str> {
    // ASCII except for control characters, special symbols in Ferrisp, brackets,
    // `.`, and whitespace.
    let chars = "!#$%&*+-/0123456789<=>?ABCDEFGHIJKLMNOPQRSTUVWXYZ_abcdefghijklmnopqrstuvwxyz";
    take_while1(move |c| chars.contains(c))(i)
}

fn special<'a>(i: &'a str) -> IResult<&'a str, &'a str> {
    alt((tag("`"), tag("'"), tag("~")))(i)
}

fn bool<'a>(i: &'a str) -> IResult<&'a str, &'a str> {
    alt((tag("true"), tag("false")))(i)
}

fn nil<'a>(i: &'a str) -> IResult<&'a str, &'a str> {
    tag("nil")(i)
}

fn truthy_nil<'a>(i: &'a str) -> IResult<&'a str, &'a str> {
    terminated(alt((bool, nil)), multispace1)(i)
}

fn neg_int<'a>(i: &'a str) -> IResult<&'a str, &'a str> {
    preceded(tag("-"), digit1)(i)
}

fn integer<'a>(i: &'a str) -> IResult<&'a str, i64> {
    alt((
        map_res(recognize(neg_int), |s: &str| s.parse::<i64>()),
        map_res(digit1, |s: &str| s.parse::<i64>()),
    ))(i)
}

fn comment<'a>(i: &'a str) -> IResult<&'a str, &'a str> {
    preceded(take_while1(|s: char| s == ';'), is_not("\r\n"))(i)
}

fn esc_str<'a>(i: &'a str) -> IResult<&'a str, &'a str> {
    escaped(valid_str, '\\', one_of(r#""n\"#))(i)
}

fn delim_esc<'a>(i: &'a str) -> IResult<&'a str, &'a str> {
    delimited(tag("\""), esc_str, tag("\""))(i)
}

fn trans_string<'a>(i: &'a str) -> IResult<&'a str, String> {
    // println!("fn string: {:?}", i);
    escaped_transform(valid_str, '\\', |s: &str| {
        alt((
            value("\\", tag("\\")),
            value("\"", tag("\"")),
            value("\n", tag("n")),
        ))(s)
    })(i)
}

fn str_lit<'a>(i: &'a str) -> IResult<&'a str, String> {
    alt((
        value(i.to_owned(), tag(r#""""#)),
        map_parser(delim_esc, trans_string),
    ))(i)
}

fn kw<'a>(i: &'a str) -> IResult<&'a str, String> {
    map(preceded(tag(":"), valid_symbols), |s: &str| s.to_string())(i)
}

#[cfg(test)]
mod tests {
    use crate::parser::*;
    use nom::error::ErrorKind;
    use nom::Err::Error;

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
        let bad_but_valid_identifier = "trueFudge";
        let true_ws = "true ";
        let nil_crlf = "nil\r\n";
        let false_tab = "false\t";

        assert_eq!(
            truthy_nil(bad_but_valid_identifier),
            Err(Error(("Fudge", ErrorKind::MultiSpace)))
        );
        assert_eq!(truthy_nil(true_ws), Ok(("", "true")));
        assert_eq!(truthy_nil(nil_crlf), Ok(("", "nil")));
        assert_eq!(truthy_nil(false_tab), Ok(("", "false")));
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
}
