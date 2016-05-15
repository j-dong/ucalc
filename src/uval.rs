use unit::*;
use value::*;
use rational::OverflowError;
use std::cmp;

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct UnitValue {
    pub value: Value,
    pub unit: Unit,
}

impl From<OverflowError> for ArithmeticError {
    fn from(_: OverflowError) -> ArithmeticError {
        ArithmeticError::OverflowError
    }
}

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
    pub fn unitless(&self) -> bool {
        self.unit == Unit::zero()
    }
    pub fn add(&self, other: &UnitValue) -> Result<UnitValue, ArithmeticError> {
        if self.unit == other.unit {
            Ok(UnitValue {
                value: try!(self.value.add(&other.value)),
                unit: self.unit,
            })
        } else {
            Err(ArithmeticError::UnitError)
        }
    }
    pub fn sub(&self, other: &UnitValue) -> Result<UnitValue, ArithmeticError> {
        if self.unit == other.unit {
            Ok(UnitValue {
                value: try!(self.value.sub(&other.value)),
                unit: self.unit,
            })
        } else {
            Err(ArithmeticError::UnitError)
        }
    }
    pub fn mul(&self, other: &UnitValue) -> Result<UnitValue, ArithmeticError> {
        Ok(UnitValue {
            value: try!(self.value.mul(&other.value)),
            unit: try!(self.unit.add(&other.unit)),
        })
    }
    pub fn div(&self, other: &UnitValue) -> Result<UnitValue, ArithmeticError> {
        Ok(UnitValue {
            value: try!(self.value.div(&other.value)),
            unit: try!(self.unit.sub(&other.unit)),
        })
    }
    pub fn pow(&self, other: &UnitValue) -> Result<UnitValue, ArithmeticError> {
        if other.unitless() {
            if self.unitless() {
                Ok(UnitValue {
                    value: try!(self.value.pow(&other.value)),
                    unit: Unit::zero(),
                })
            } else {
                match other.value.get_exact() {
                    Some(e) => Ok(UnitValue {
                        value: try!(self.value.pow(&other.value)),
                        unit: try!(self.unit.mul(e)),
                    }),
                    None => Err(ArithmeticError::UnitError),
                }
            }
        } else {
            Err(ArithmeticError::UnitError)
        }
    }
}
