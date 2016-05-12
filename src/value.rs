use rational::*;

use std::cmp;
use std::cmp::Ord;

#[derive(Copy, Clone, Hash, Debug)]
enum Value {
    Float(f64),
    Rational(f64),
}

impl PartialEq for Value {
    #[inline]
    fn eq(&self, other: &PartialEq) -> bool {
        self.cmp(other) == cmp::Ordering::Equal
    }
    #[inline]
    fn ne(&self, other: &PartialEq) -> bool {
        self.cmp(other) != cmp::Ordering::Equal
    }
}

impl Eq for Value {}

impl Ord for Value {
    fn cmp(&self, other: &Value) -> cmp::Ordering {
        match (self, other) {
            &Value::Float(ref a), &Value::Float(ref b) => a.partial_cmp(b).unwrap_or(cmp::Ordering::Equal),
            &Value::Rational(ref a), // TODO: rest
        }
    }
}

impl PartialOrd for Value {
    fn partial_cmp(&self, other: &Value) -> Option<cmp::Ordering> {
        Some(self.cmp(other))
    }
}
