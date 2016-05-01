#![feature(box_patterns)]
#[macro_use]
extern crate nom;

use nom::{digit, IResult};

use std::str;
use std::str::FromStr;

#[derive(Debug)]
enum Expression {
    Value(f64),
    Exp(Box<Expression>, Box<Expression>),
    Mul(Box<Expression>, Box<Expression>),
    Div(Box<Expression>, Box<Expression>),
    Add(Box<Expression>, Box<Expression>),
    Sub(Box<Expression>, Box<Expression>),
}

named!(parens<Expression>, delimited!(char!('('), /* expr */fac, char!(')')));

named!(number<f64>, map_res!(map_res!(digit, str::from_utf8), FromStr::from_str));

named!(atom<Expression>, alt!(number => {Expression::Value} | parens));

named!(exp<Expression>, dbg_dmp!(chain!(lhs: atom ~ rhs: preceded!(char!('^'), exp)?, ||{
    match (lhs, rhs) {
        (lhs, None) => lhs,
        (Expression::Value(a), Some(Expression::Value(b))) => Expression::Value(a.powf(b)),
        (lhs, Some(b)) => Expression::Exp(Box::new(lhs), Box::new(b)),
    }
})));

named!(fac<Expression>, dbg_dmp!(chain!(first: exp ~ others: many0!(tuple!(alt!(char!('*') | char!('/')), exp)), ||{
    others.into_iter().fold(first, |lhs, (op, rhs)| simplify1(match op { '*' => Expression::Mul(Box::new(lhs), Box::new(rhs)), '/' => Expression::Div(Box::new(lhs), Box::new(rhs)), _ => Expression::Mul(Box::new(lhs), Box::new(rhs))}))
})));

named!(input<Expression>, dbg_dmp!(chain!(res: fac ~ char!('?'), ||{res})));

fn simplify1(expr: Expression) -> Expression {
    match expr {
        Expression::Exp(box Expression::Value(a), box Expression::Value(b)) => Expression::Value(a.powf(b)),
        Expression::Mul(box Expression::Value(a), box Expression::Value(b)) => Expression::Value(a * b),
        Expression::Div(box Expression::Value(a), box Expression::Value(b)) => Expression::Value(a / b),
        Expression::Add(box Expression::Value(a), box Expression::Value(b)) => Expression::Value(a + b),
        Expression::Sub(box Expression::Value(a), box Expression::Value(b)) => Expression::Value(a - b),
        expr => expr
    }
}

fn main() {
    println!("A: {:?}", exp(b"1?"));
    println!("A: {:?}", fac(b"1*1?"));
    println!("A: {:?}", fac(b"1/2*3?"));
    println!("A: {:?}", fac(b"1^1?"));
    println!("A: {:?}", fac(b"1^1^1?"));
    println!("Result: {:?}", fac(b"2/3^5*2^1^2?"));
}
