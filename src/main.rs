#![feature(box_patterns)]
#[macro_use]
extern crate nom;

use nom::{multispace, alpha, IResult};

use std::str;

#[derive(Debug, PartialEq)]
enum Expression {
    Value(f64),
    Exp(Box<Expression>, Box<Expression>),
    Mul(Box<Expression>, Box<Expression>),
    Div(Box<Expression>, Box<Expression>),
    Add(Box<Expression>, Box<Expression>),
    Sub(Box<Expression>, Box<Expression>),
    Neg(Box<Expression>),
}

fn get_unary_function(res: &[u8]) -> Option<Box<Fn(f64) -> f64>> {
    match res {
        "sin" => Some(Box::new(f64::sin)),
        "cos" => Some(Box::new(f64::cos)),
        "tan" => Some(Box::new(f64::tan)),
        _ => None
    }
}

fn get_function(res: &[u8]) -> Option<Box<Fn(Vec<f64>) -> f64>> {
    if let Some(f) = get_unary_function(res) {
        return Some(Box::new(|a: Vec<f64>| f(a[0])))
    }
}

named!(parens<Expression>, dbg_dmp!(delimited!(char!('('), preceded!(opt!(multispace), expr), preceded!(opt!(multispace), char!(')')))));

named!(decimal<()>, value!((), many1!(one_of!("0123456789_"))));
#[inline]
named!(recognize_number1<&[u8]>, recognize!(chain!(decimal ~ preceded!(char!('.'), opt!(decimal))? ~ preceded!(one_of!("eE"), preceded!(opt!(one_of!("+-")), decimal))?, || ())));
#[inline]
named!(recognize_number2<&[u8]>, recognize!(chain!(char!('.') ~ decimal ~ preceded!(one_of!("eE"), preceded!(opt!(one_of!("+-")), decimal))?, || ())));
#[inline]
fn stringify_u8(res: &[u8]) -> Result<String, str::Utf8Error> {
    Ok(try!(str::from_utf8(res)).to_owned())
}
#[inline]
fn prepend_zero(res: &[u8]) -> Result<String, str::Utf8Error> {
    let mut s = try!(str::from_utf8(res)).to_owned();
    s.insert(0, '0');
    Ok(s)
}

named!(number<f64>, dbg_dmp!(map_res!(map_res!(alt!(recognize_number1 => {stringify_u8}
                                                  | recognize_number2 => {prepend_zero}),
                                              |a: Result<String, str::Utf8Error>| Ok(try!(a).replace('_', "")) as Result<String, str::Utf8Error>), |a: String| a.parse())));

fn get_numerical_constant(res: &[u8]) -> Option<f64> {
    match &res {
        &b"e" => Some(std::f64::consts::E),
        &b"pi" => Some(std::f64::consts::PI),
        _ => None
    }
}

#[inline]
named!(num_const<f64>, map_opt!(alpha, get_numerical_constant));

named!(atom<Expression>, dbg_dmp!(alt!(parens | alt!(number | num_const) => {Expression::Value})));

named!(imul<Expression>, dbg_dmp!(chain!(first: atom ~ others: many0!(atom), ||
    others.into_iter().fold(first, |lhs, rhs| simplify1(Expression::Mul(Box::new(lhs), Box::new(rhs))))
)));

named!(unary<Expression>, dbg_dmp!(alt!(exp | chain!(op: chain!(o: alt!(char!('+') | char!('-')) ~ multispace?, || o) ~ val: unary, ||{
    match op {
        '+' => val,
        '-' => simplify1(Expression::Neg(Box::new(val))),
        _ => val,
    }
}))));

named!(exp<Expression>, dbg_dmp!(chain!(lhs: imul ~ rhs: preceded!(preceded!(opt!(multispace), char!('^')), preceded!(opt!(multispace), unary))?, ||{
    match (lhs, rhs) {
        (lhs, None) => lhs,
        (Expression::Value(a), Some(Expression::Value(b))) => Expression::Value(a.powf(b)),
        (lhs, Some(b)) => Expression::Exp(Box::new(lhs), Box::new(b)),
    }
})));

named!(facterm<(char, Expression)>,
        tuple!(alt!(
                preceded!(opt!(multispace), char!('*'))
              | preceded!(opt!(multispace), char!('/'))
              | value!('*', preceded!(multispace, error!(nom::ErrorKind::NoneOf, peek!(none_of!("+-")))))), preceded!(opt!(multispace), unary)));

named!(fac<Expression>, dbg_dmp!(
        chain!(first: unary
             ~ others: many0!(facterm), ||
    others.into_iter().fold(first, |lhs, (op, rhs)| simplify1(
            match op {
                '*' => Expression::Mul(Box::new(lhs), Box::new(rhs)),
                '/' => Expression::Div(Box::new(lhs), Box::new(rhs)),
                _   => Expression::Mul(Box::new(lhs), Box::new(rhs))
            }))
)));

named!(expr<Expression>, dbg_dmp!(
        chain!(first: fac
             ~ others: many0!(tuple!(
                       preceded!(opt!(multispace), alt!(char!('+') | char!('-'))), preceded!(opt!(multispace), fac))), ||
    others.into_iter().fold(first, |lhs, (op, rhs)| simplify1(
            match op {
                '+' => Expression::Add(Box::new(lhs), Box::new(rhs)),
                '-' => Expression::Sub(Box::new(lhs), Box::new(rhs)),
                _   => Expression::Add(Box::new(lhs), Box::new(rhs))
            }))
)));

named!(input<Expression>, dbg_dmp!(chain!(opt!(multispace) ~ res: expr ~ opt!(multispace) ~ char!('?'), ||{res})));

fn simplify1(expr: Expression) -> Expression {
    match expr {
        Expression::Exp(box Expression::Value(a), box Expression::Value(b)) => Expression::Value(a.powf(b)),
        Expression::Mul(box Expression::Value(a), box Expression::Value(b)) => Expression::Value(a * b),
        Expression::Div(box Expression::Value(a), box Expression::Value(b)) => Expression::Value(a / b),
        Expression::Add(box Expression::Value(a), box Expression::Value(b)) => Expression::Value(a + b),
        Expression::Sub(box Expression::Value(a), box Expression::Value(b)) => Expression::Value(a - b),
        Expression::Neg(box Expression::Value(a)) => Expression::Value(-a),
        Expression::Neg(box Expression::Neg(box a)) => a,
        expr => expr
    }
}

macro_rules! test_expr {
    ( $x:expr, $v: expr) => (assert_eq!(input(concat!($x, "?").as_bytes()), IResult::Done(&b""[..], Expression::Value($v))));
}
macro_rules! fail_expr {
    ( $x: expr ) => (match input(concat!($x, "?").as_bytes()) { IResult::Done(_, _) => panic!("should have failed"), _ => () })
}

#[test]
fn test_exponents() {
    test_expr!("2^1^5", 2.0);
}

#[test]
fn test_muldiv() {
    test_expr!("2*3", 6.0);
    test_expr!("3/2", 1.5);
    test_expr!("3/2*4", 6.0);
    test_expr!("2^2*3", 12.0);
    test_expr!("2 2 2 ", 8.0);
}

#[test]
fn test_implied_mul() {
    test_expr!("1/2(4)", 0.125);
    test_expr!("1/2 (4)", 2.0);
    test_expr!("1(2)3(4)5(6)7(8)9(10)", 3628800.0)
}

#[test]
fn test_addsub() {
    test_expr!("1+1", 2.0);
    test_expr!("3-2", 1.0);
    test_expr!("3-2+3", 4.0);
    test_expr!("2^3*4-5", 27.0);
}

#[test]
fn test_whitespace() {
    test_expr!(" (2^39)* 122/2 + 80 -1023 ", 33535104646225.0);
    test_expr!("(    2     ^   1   )   * 5    / 2 +   3    - 5", 3.0);
}

#[test]
fn test_huge() {
    test_expr!("(((17 - 9 - 14) / 1 + 13 * 15) / 5 / 8 - 18) / 11 * 15 * 17 / (16 / 5 + 10 * 16 / ((5 / 14 - 3 - 4 - 6) * (9 * 7 / 2 - 7 - 16)))", -179.844926355302559466636533137465393525057912876433696);
}

#[test]
fn test_unary() {
    test_expr!("1+-1(2)", -1.0);
    test_expr!("1/2-2", -1.5);
    test_expr!("1+1", 2.0);
    test_expr!("1 + 1", 2.0);
    test_expr!("1+1/-(3-2)", 0.0);
    test_expr!("-2^2", -4.0);
    test_expr!("2^-2", 0.25);
    test_expr!("-2(5)", -10.0);
}

#[test]
fn test_thomas() {
    test_expr!("1+1", 2.0);
    test_expr!("2^(3*2-4)-4", 0.0);
}

#[test]
fn test_floating() {
    test_expr!("5", 5.0);
    test_expr!("2.3e2", 230.0);
    test_expr!("5e-2", 0.05);
    test_expr!("8_230_999", 8_230_999.0);
    fail_expr!("_");
    test_expr!(".2", 0.2);
    // Rust reference examples
    test_expr!("123.0", 123.0f64);
    test_expr!("0.1", 0.1f64);
    test_expr!("12E+99", 12E+99_f64);
    test_expr!("2.", 2.);
}

#[test]
fn test_num_const() {
    test_expr!("pi", std::f64::consts::PI);
    test_expr!("e", std::f64::consts::E);
}

fn main() {
    println!("A: {:?}", input(b"1?"));
    println!("A: {:?}", input(b"1*1?"));
    println!("A: {:?}", input(b"1/2*3?"));
    println!("A: {:?}", input(b"1^1?"));
    println!("A: {:?}", input(b"1^1^1?"));
    println!("Result: {:?}", input(b"2/3^5*2^1^2?"));
}
