use rational::*;

use std::cmp;
use std::ops::{Add,Sub,Mul,Neg};
use std::fmt;

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Unit {
    pub m: Rational,
    pub kg: Rational,
    pub s: Rational,
    pub a: Rational,
    pub k: Rational,
    pub cd: Rational,
    pub mol: Rational,
}

impl Unit {
    pub fn zero() -> Unit {
        Unit {
            m: Rational::zero(),
            kg: Rational::zero(),
            s: Rational::zero(),
            a: Rational::zero(),
            k: Rational::zero(),
            cd: Rational::zero(),
            mol: Rational::zero(),
        }
    }
    // may overflow
    pub fn add(&self, other: &Unit) -> Result<Unit, OverflowError> {
        Ok(Unit {
            m: try!(self.m.add(&other.m)),
            kg: try!(self.kg.add(&other.kg)),
            s: try!(self.s.add(&other.s)),
            a: try!(self.a.add(&other.a)),
            k: try!(self.k.add(&other.k)),
            cd: try!(self.cd.add(&other.cd)),
            mol: try!(self.mol.add(&other.mol)),
        })
    }
    pub fn sub(&self, other: &Unit) -> Result<Unit, OverflowError> {
        Ok(Unit {
            m: try!(self.m.sub(&other.m)),
            kg: try!(self.kg.sub(&other.kg)),
            s: try!(self.s.sub(&other.s)),
            a: try!(self.a.sub(&other.a)),
            k: try!(self.k.sub(&other.k)),
            cd: try!(self.cd.sub(&other.cd)),
            mol: try!(self.mol.sub(&other.mol)),
        })
    }
    pub fn mul(&self, other: &Rational) -> Result<Unit, OverflowError> {
        Ok(Unit {
            m: try!(self.m.mul(&other)),
            kg: try!(self.kg.mul(&other)),
            s: try!(self.s.mul(&other)),
            a: try!(self.a.mul(&other)),
            k: try!(self.k.mul(&other)),
            cd: try!(self.cd.mul(&other)),
            mol: try!(self.mol.mul(&other)),
        })
    }
}

impl Add for Unit {
    type Output = Unit;
    fn add(self, other: Unit) -> Unit {
        (&self).add(&other).expect("unit overflow")
    }
}

impl Sub for Unit {
    type Output = Unit;
    fn sub(self, other: Unit) -> Unit {
        (&self).sub(&other).expect("unit overflow")
    }
}

impl Mul<Rational> for Unit {
    type Output = Unit;
    fn mul(self, other: Rational) -> Unit {
        (&self).mul(&other).expect("unit overflow")
    }
}

impl Neg for Unit {
    type Output = Unit;
    fn neg(self) -> Unit {
        Unit {
            m: -self.m,
            kg: -self.kg,
            s: -self.s,
            a: -self.a,
            k: -self.k,
            cd: -self.cd,
            mol: -self.mol,
        }
    }
}
