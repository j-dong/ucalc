//! Value module. Can be exact or inexact.

use rational::*;

use std::cmp;
use std::cmp::Ord;
use std::ops::{Add,Sub,Mul,Div,Neg};
use std::fmt;

/// Value type. A Value is either exact or inexact.
/// All values are valid numbers and are not Infinity or NaN.
#[derive(Copy, Clone, Debug)]
pub enum Value {
    /// An inexact (floating-point) value
    Inexact(f64),
    /// An exact (rational) value
    Exact(Rational),
}

impl AsFloat for Value {
    #[inline]
    fn as_float(&self) -> f64 {
        match self {
            &Value::Inexact(a) => a,
            &Value::Exact(ref a) => a.as_float(),
        }
    }
}

impl PartialEq for Value {
    // two values can be equal even if they are not identical, so we must implement these methods
    // ourselves.
    // we just use the cmp method we already implemented.
    #[inline]
    fn eq(&self, other: &Value) -> bool {
        self.cmp(other) == cmp::Ordering::Equal
    }
    #[inline]
    fn ne(&self, other: &Value) -> bool {
        self.cmp(other) != cmp::Ordering::Equal
    }
}

impl Eq for Value {}

impl Ord for Value {
    fn cmp(&self, other: &Value) -> cmp::Ordering {
        match (self, other) {
            // compare two values (guaranteed to be non-NaN)
            (&Value::Inexact(ref a), &Value::Inexact(ref b)) => a.partial_cmp(b).unwrap(),
            // compare two exact values
            (&Value::Exact(ref a), &Value::Exact(ref b)) => a.cmp(b),
            // otherwise, convert one to float first
            (a, b) => a.as_float().partial_cmp(&b.as_float()).unwrap(),
        }
    }
}

impl PartialOrd for Value {
    fn partial_cmp(&self, other: &Value) -> Option<cmp::Ordering> {
        Some(self.cmp(other))
    }
}

// includes unit errors
/// An error caused by an arithmetic operator.
#[derive(Debug, PartialEq, Eq, Hash, Copy, Clone)]
pub enum ArithmeticError {
    /// Caused by division by zero
    DivideByZeroError,
    /// Caused by an invalid argument
    DomainError,
    /// Caused by overflow
    OverflowError,
    /// Incompatible units or invalid use of units
    UnitError,
}

impl Value {
    /// Used for user input; approximates values that could be represented exactly (denominator 8)
    pub fn from_input(f: f64) -> Result<Value, ArithmeticError> {
        if !f.is_nan() && !f.is_infinite() {
            if (f * 8.0).fract() != 0.0 {
                Ok(Value::Inexact(f))
            } else {
                let num = f * 8.0;
                // if it can be represented exactly as a Rational, use that
                if num.abs() > i32::max_value() as f64 {
                    Ok(Value::Inexact(f))
                } else {
                    Rational::new(num as i32, 8).or(Err(ArithmeticError::DomainError)).map(Value::Exact)
                }
            }
        } else {
            // infinite values are overflow, NaN values are invalid
            if f.is_infinite() {
                Err(ArithmeticError::OverflowError)
            } else {
                Err(ArithmeticError::DomainError)
            }
        }
    }
    /// Convert a float into a Value, directly using the Inexact form. (Still checks for error)
    #[inline]
    pub fn from_float(f: f64) -> Result<Value, ArithmeticError> {
        if !f.is_nan() && !f.is_infinite() {
            Ok(Value::Inexact(f))
        } else {
            if f.is_infinite() {
                Err(ArithmeticError::OverflowError)
            } else {
                Err(ArithmeticError::DomainError)
            }
        }
    }
    /// Get as an exact value (returns None if inexact)
    #[inline]
    pub fn get_exact(&self) -> Option<&Rational> {
        match self {
            &Value::Exact(ref a) => Some(a),
            &Value::Inexact(_) => None,
        }
    }
    /// Converts self into an integer if possible.
    #[inline]
    pub fn as_integer(&self) -> Option<i32> {
        match self {
            &Value::Exact(ref a) => if a.is_integer() { Some(a.num) } else { None },
            &Value::Inexact(a) => if a.fract() == 0.0 && a.abs() <= i32::max_value() as f64 { Some(a as i32) } else { None },
        }
    }
    /// Zero value
    #[inline]
    pub fn zero() -> Value {
        Value::Exact(Rational::zero())
    }
    /// Check if zero
    #[inline]
    pub fn is_zero(&self) -> bool {
        match self {
            &Value::Exact(ref a) => a.is_zero(),
            &Value::Inexact(a) => a == 0.0,
        }
    }
    pub fn add(&self, other: &Value) -> Result<Value, ArithmeticError> {
        match (self.get_exact(), other.get_exact()) {
            // special case for two exact values
            (Some(a), Some(b)) => a.add(b).map(Value::Exact).or_else(|_| Value::from_float(self.as_float() + other.as_float())),
            _ => Value::from_float(self.as_float() + other.as_float())
        }
    }
    pub fn sub(&self, other: &Value) -> Result<Value, ArithmeticError> {
        match (self.get_exact(), other.get_exact()) {
            // special case for two exact values
            (Some(a), Some(b)) => a.sub(b).map(Value::Exact).or_else(|_| Value::from_float(self.as_float() - other.as_float())),
            _ => Value::from_float(self.as_float() - other.as_float())
        }
    }
    pub fn mul(&self, other: &Value) -> Result<Value, ArithmeticError> {
        match (self.get_exact(), other.get_exact()) {
            // special case for two exact values'
            (Some(a), Some(b)) => a.mul(b).map(Value::Exact).or_else(|_| Value::from_float(self.as_float() * other.as_float())),
            _ => Value::from_float(self.as_float() * other.as_float())
        }
    }
    pub fn div(&self, other: &Value) -> Result<Value, ArithmeticError> {
        if other.as_float() == 0.0 { // divide by zero
            return Err(ArithmeticError::DivideByZeroError);
        }
        match (self.get_exact(), other.get_exact()) {
            // special case for two exact values
            (Some(a), Some(b)) => a.div(b).map(Value::Exact).or_else(|_| Value::from_float(self.as_float() / other.as_float())),
            _ => Value::from_float(self.as_float() / other.as_float())
        }
    }
    pub fn pow(&self, other: &Value) -> Result<Value, ArithmeticError> {
        match self.get_exact() {
            // if other is an integer, exponentiate rationally (unless overflow). otherwise, inexact
            Some(a) => if let Some(e) = other.as_integer() { a.pow(e).map(Value::Exact).or_else(|_| Value::from_float(a.as_float().powi(e))) } else { Value::from_float(a.as_float().powf(other.as_float())) },
            None => Value::from_float(self.as_float().powf(other.as_float()))
        }
    }
}

// arithmetic traits
impl Add for Value {
    type Output = Value;
    fn add(self, other: Value) -> Value {
        (&self).add(&other).unwrap()
    }
}

impl Sub for Value {
    type Output = Value;
    fn sub(self, other: Value) -> Value {
        (&self).sub(&other).unwrap()
    }
}

impl Mul for Value {
    type Output = Value;
    fn mul(self, other: Value) -> Value {
        (&self).mul(&other).unwrap()
    }
}

impl Div for Value {
    type Output = Value;
    fn div(self, other: Value) -> Value {
        (&self).div(&other).unwrap()
    }
}

impl Neg for Value {
    type Output = Value;
    fn neg(self) -> Value {
        match self {
            Value::Exact(a) => Value::Exact(-a),
            Value::Inexact(a) => Value::Inexact(-a),
        }
    }
}

/// Format as inexact or exact
impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            &Value::Inexact(a) => write!(f, "{}", a),
            &Value::Exact(ref a) => write!(f, "{}", a),
        }
    }
}

/// Self-explanatory tests
#[cfg(test)]
mod tests {
    use super::*;
    use rational::*;

    #[test]
    fn test_as_float() {
        for a in vec![0.0, -0.0, 8.0, 0.125, 10e100] {
            assert_eq!(Value::from_input(a).unwrap().as_float(), a);
        }
    }

    // value macro
    macro_rules! val {
        ( V $a:expr ) => ( Value::from_input($a).unwrap() )
    }

    #[test]
    fn test_simple_arithmetic() {
        assert_eq!(val!(V 4.0) + val!(V 1.0), val!(V 5.0));
        assert_eq!(val!(V 4.0) - val!(V 1.0), val!(V 3.0));
        assert_eq!(val!(V 4.0) * val!(V 1.0), val!(V 4.0));
        assert_eq!(val!(V 4.0) / val!(V 2.0), val!(V 2.0));
    }
}
