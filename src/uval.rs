//! Value with units. Ties together unit and value.

use unit::*;
use value::*;
use rational::{OverflowError,AsFloat};
use std::cmp;
use std::ops::{Add,Sub,Mul,Div,Neg};
use std::fmt;

/// A value with units
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct UnitValue {
    /// Numerical value
    pub value: Value,
    /// Unit
    pub unit: Unit,
}

impl From<OverflowError> for ArithmeticError {
    /// Convert an OverflowError (from Rational) to a value's ArithmeticError
    fn from(_: OverflowError) -> ArithmeticError {
        ArithmeticError::OverflowError
    }
}

/// UnitValues can be compared only if units correspond
impl PartialOrd for UnitValue {
    #[inline]
    fn partial_cmp(&self, other: &UnitValue) -> Option<cmp::Ordering> {
        if self.unit == other.unit {
            self.value.partial_cmp(&other.value)
        } else {
            None
        }
    }
}

impl AsFloat for UnitValue {
    /// Convert into a float (only valid for unitless quantities)
    #[inline]
    fn as_float(&self) -> f64 {
        if !self.unitless() {
            println!("treating as unitless");
        }
        self.value.as_float()
    }
}

// see value.rs for descriptions of these methods
impl UnitValue {
    #[inline]
    pub fn from_input(f: f64) -> Result<UnitValue, ArithmeticError> {
        Ok(UnitValue {
            value: try!(Value::from_input(f)),
            unit: Unit::zero(),
        })
    }
    #[inline]
    pub fn from_float(f: f64) -> Result<UnitValue, ArithmeticError> {
        Ok(UnitValue {
            value: try!(Value::from_float(f)),
            unit: Unit::zero(),
        })
    }
    #[inline]
    pub fn zero() -> UnitValue {
        UnitValue {value: Value::zero(), unit: Unit::zero()}
    }
    #[inline]
    pub fn is_zero(&self) -> bool {
        self.value.is_zero()
    }
    /// zero values are always unitless; check for that
    #[inline]
    fn checked_uval(value: Value, unit: Unit) -> UnitValue {
        if value.is_zero() {
            UnitValue::zero()
        } else {
            UnitValue {value: value, unit: unit}
        }
    }
    /// is this value unitless
    #[inline]
    pub fn unitless(&self) -> bool {
        self.unit == Unit::zero()
    }
    pub fn add(&self, other: &UnitValue) -> Result<UnitValue, ArithmeticError> {
        // check that units correspond
        if self.unit == other.unit {
            Ok(UnitValue::checked_uval(
                try!((&self.value).add(&other.value)),
                self.unit,
            ))
        } else {
            // check for zero
            if self.is_zero() {
                return Ok(other.clone())
            }
            if other.is_zero() {
                return Ok(self.clone())
            }
            Err(ArithmeticError::UnitError)
        }
    }
    pub fn sub(&self, other: &UnitValue) -> Result<UnitValue, ArithmeticError> {
        // check that units correspond
        if self.unit == other.unit {
            Ok(UnitValue::checked_uval(
                try!((&self.value).sub(&other.value)),
                self.unit,
            ))
        } else {
            // check for zero
            if self.is_zero() {
                return Ok(other.clone())
            }
            if other.is_zero() {
                return Ok(self.clone())
            }
            Err(ArithmeticError::UnitError)
        }
    }
    pub fn mul(&self, other: &UnitValue) -> Result<UnitValue, ArithmeticError> {
        Ok(UnitValue {
            value: try!((&self.value).mul(&other.value)),
            unit: try!((&self.unit).add(&other.unit)),
        })
    }
    pub fn div(&self, other: &UnitValue) -> Result<UnitValue, ArithmeticError> {
        Ok(UnitValue {
            value: try!((&self.value).div(&other.value)),
            unit: try!((&self.unit).sub(&other.unit)),
        })
    }
    pub fn pow(&self, other: &UnitValue) -> Result<UnitValue, ArithmeticError> {
        if other.unitless() {
            if self.unitless() {
                // any number can be raised to any power if both unitless
                Ok(UnitValue {
                    value: try!((&self.value).pow(&other.value)),
                    unit: Unit::zero(),
                })
            } else {
                // otherwise, only rational powers are allowed
                match other.value.get_exact() {
                    Some(e) => Ok(UnitValue {
                        value: try!((&self.value).pow(&other.value)),
                        unit: try!((&self.unit).mul(e)),
                    }),
                    None => Err(ArithmeticError::UnitError),
                }
            }
        } else {
            Err(ArithmeticError::UnitError)
        }
    }
}

// arithmetic traits
impl Add for UnitValue {
    type Output = UnitValue;
    fn add(self, other: UnitValue) -> UnitValue {
        (&self).add(&other).unwrap()
    }
}

impl Sub for UnitValue {
    type Output = UnitValue;
    fn sub(self, other: UnitValue) -> UnitValue {
        (&self).sub(&other).unwrap()
    }
}

impl Mul for UnitValue {
    type Output = UnitValue;
    fn mul(self, other: UnitValue) -> UnitValue {
        (&self).mul(&other).unwrap()
    }
}

impl Div for UnitValue {
    type Output = UnitValue;
    fn div(self, other: UnitValue) -> UnitValue {
        (&self).div(&other).unwrap()
    }
}

impl Neg for UnitValue {
    type Output = UnitValue;
    fn neg(self) -> UnitValue {
        UnitValue {
            value: -self.value,
            unit: self.unit,
        }
    }
}

impl fmt::Display for UnitValue {
    /// Display value followed by unit (unless unitless)
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        if self.unitless() {
            write!(f, "{}", self.value)
        } else {
            write!(f, "{} {}", self.value, self.unit)
        }
    }
}
