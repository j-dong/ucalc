use rational::*;

use std::cmp;
use std::cmp::Ord;
use std::fmt;

#[derive(Copy, Clone, Debug)]
pub enum Value {
    Inexact(f64),
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
            (&Value::Inexact(ref a), &Value::Inexact(ref b)) => a.partial_cmp(b).unwrap(),
            (&Value::Exact(ref a), &Value::Exact(ref b)) => a.cmp(b),
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
#[derive(Debug, PartialEq, Eq, Hash)]
enum ArithmeticError {
    DivideByZeroError,
    DomainError,
    OverflowError,
}

impl Value {
    fn from_float(f: f64) -> Result<Value, ArithmeticError> {
        if !f.is_nan() {
            if (f * 8.0).fract() != 0.0 {
                Ok(Value::Inexact(f))
            } else {
                let num = f * 8.0;
                if num.abs() > i32::max_value() as f64 {
                    Ok(Value::Inexact(f))
                } else {
                    Rational::new(num as i32, 8).or(Err(ArithmeticError::DomainError)).map(Value::Exact)
                }
            }
        } else {
            Err(ArithmeticError::DomainError)
        }
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            &Value::Inexact(a) => write!(f, "{}", a),
            &Value::Exact(ref a) => write!(f, "{}", a),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rational::*;
    use std::f64;
    use std::cmp;
    use std::cmp::Ordering;
    use std::fmt;
    use std::fmt::{Write, Display};

    #[test]
    fn test_as_float() {
        for a in vec![f64::INFINITY, -f64::INFINITY, 0.0, -0.0, 8.0, 0.125, 10e100] {
            assert_eq!(Value::from_float(a).unwrap().as_float(), a);
        }
    }
}
