use std::ops::Neg;
use std::cmp;
use std::cmp::Ord;
use std::fmt;

/// Rational numbers. The following are invariants:
///
/// * Both numerator and denominator are between `i32::min_value() + 1`
///   and `i32::max_value()`, inclusive. (This is so that negation and
///   casting between `i32` and `u32` are always valid.) Any operation
///   that would cause this to be false would return `Err(OverflowError)`.
/// * The denominator is always positive. An operation that would
///   cause the denominator to be zero would return `Err(OverflowError)`.
#[derive(Copy, Clone, Hash, Debug, PartialEq, Eq)]
pub struct Rational {
    pub num: i32,
    pub den: u32,
}

#[derive(Debug, PartialEq, Eq)]
pub struct OverflowError;

#[inline]
fn checked_pow(mut base: i32, mut exp: u32) -> Result<i32, OverflowError> {
    let mut acc: i32 = 1;
    while exp > 1 {
        if (exp & 1) == 1 {
            acc = try!(acc.checked_mul(base).ok_or(OverflowError));
        }
        exp /= 2;
        base = try!(base.checked_mul(base).ok_or(OverflowError));
    }
    if exp == 1 {
        acc = try!(acc.checked_mul(base).ok_or(OverflowError));
    }
    Ok(acc)
}

/// Find the greatest common divisor of two integers.
/// The result has the same sign as the denominator `n`, or the sign
/// of the numerator `m` if it is zero.
/// Copied from [`num`](https://github.com/rust-num/num) crate
/// (MIT/Apache License).
// Here's the license: (I have modified the function by making it
// return the sign of the denominator)
//
// Copyright 2013-2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.:
#[inline]
fn gcd(mut m: i32, mut n: i32) -> i32 {
    // Use Stein's algorithm
    if m == 0 || n == 0 { return m | n }

    // find common factors of 2
    let shift = (m | n).trailing_zeros();

    // The algorithm needs positive numbers, but the minimum value
    // can't be represented as a positive one.
    // It's also a power of two, so the gcd can be
    // calculated by bitshifting in that case

    // Assuming two's complement, the number created by the shift
    // is positive for all numbers except gcd = abs(min value)
    // The call to .abs() causes a panic in debug mode
    if m == i32::min_value() || n == i32::min_value() {
        return (1 << shift) as i32
    }

    // guaranteed to be positive now, rest like unsigned algorithm
    let n_sign = n.signum();
    m = m.abs();
    n = n.abs();

    // divide n and m by 2 until odd
    // m inside loop
    n >>= n.trailing_zeros();

    while m != 0 {
        m >>= m.trailing_zeros();
        if n > m { ::std::mem::swap(&mut n, &mut m) }
        m -= n;
    }

    (n << shift) * n_sign
}

trait CheckableOverflow<T> {
    fn check_overflow(self) -> Result<T, OverflowError>;
}

impl CheckableOverflow<Rational> for Rational {
    #[inline]
    fn check_overflow(self) -> Result<Rational, OverflowError> {
        if self.num > i32::min_value() && self.den > 0 && self.den <= (i32::max_value() as u32) { Ok(self) } else { Err(OverflowError) }
    }
}

impl CheckableOverflow<u32> for u32 {
    #[inline]
    fn check_overflow(self) -> Result<u32, OverflowError> {
        if self > 0 && self <= (i32::max_value() as u32) { Ok(self) } else { Err(OverflowError) }
    }
}

impl CheckableOverflow<i32> for i32 {
    #[inline]
    fn check_overflow(self) -> Result<i32, OverflowError> {
        if self > i32::min_value() { Ok(self) } else { Err(OverflowError) }
    }
}

impl<T, U> CheckableOverflow<U> for Result<T, OverflowError> where T: CheckableOverflow<U> {
    #[inline]
    fn check_overflow(self) -> Result<U, OverflowError> {
        self.and_then(CheckableOverflow::check_overflow)
    }
}

impl Neg for Rational {
    type Output = Rational;
    #[inline]
    fn neg(self) -> Rational {
        Rational {
            num: -self.num,
            den: self.den,
        }
    }
}

impl fmt::Display for Rational {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        if self.den == 1 {
            write!(f, "{}", self.num)
        } else {
            write!(f, "{}/{}", self.num, self.den)
        }
    }
}

impl Rational {
    #[inline]
    pub fn from_integer(i: i32) -> Result<Rational, OverflowError> {
        Ok(Rational {
            num: try!(i.check_overflow()),
            den: 1,
        })
    }
    pub fn new(num: i32, den: i32) -> Result<Rational, OverflowError> {
        if den == 0 {
            panic!("denominator = 0");
        }
        let gcd = gcd(num, den);
        Rational {
            num: num / gcd,
            den: (den / gcd) as u32, // guaranteed to be positive
        }.check_overflow()
    }
    #[inline]
    pub fn negate(&self) -> Rational {
        Rational {
            num: -self.num,
            den: self.den,
        }
    }
    #[inline]
    pub fn recip(&self) -> Result<Rational, OverflowError> {
        if self.num > 0 {
            Ok(Rational {
                num: self.den as i32,
                den: self.num as u32,
            })
        } else {
            if self.num != 0 {
                Ok(Rational {
                    num: -(self.den as i32),
                    den: (-self.num) as u32,
                })
            } else {
                Err(OverflowError)
            }
        }
    }
    #[inline]
    pub fn is_integer(&self) -> bool {
        self.den == 1
    }
    pub fn is_negative(&self) -> bool {
        self.num < 0
    }
    #[inline]
    pub fn pow(&self, exp: i32) -> Result<Rational, OverflowError> {
        if exp != 0 {
            if exp > 0 {
                Rational {
                    num: try!(checked_pow(self.num, exp as u32)),
                    den: try!(checked_pow(self.den as i32, exp as u32)) as u32,
                }.check_overflow()
            } else {
                if exp != i32::min_value() {
                    try!(self.pow(-exp)).recip()
                } else {
                    if (self.num == 1 || self.num == -1) && self.den == 1 {
                        Ok(Rational { num: 1, den: 1 })
                    } else {
                        Err(OverflowError)
                    }
                }
            }
        } else {
            Ok(Rational { num: 1, den: 1 })
        }
    }
    pub fn mul(&self, other: &Rational) -> Result<Rational, OverflowError> {
        match (self.num.checked_mul(other.num), (self.den as i32).checked_mul(other.den as i32)) {
            (Some(np), Some(dp)) => {
                let gcd = gcd(np, dp); // guaranteed positive
                Rational {
                    num: np / gcd,
                    den: (dp / gcd) as u32,
                }.check_overflow()
            },
            _ => {
                // (a / b) * (c / d) =
                // (a * b) / (c * d) =
                // (a / @1 * b / @2) / (c / @2 * d / @1)
                // We find n1d2 and n2d1 which are the largest
                // factors of a, d and b, c to avoid overflow as much
                // as possible.
                let n1d2 = gcd(self.num, other.den as i32);
                let n2d1 = gcd(self.den as i32, other.num);
                Rational {
                    num: try!((self.num / n1d2).checked_mul(other.num / n2d1).ok_or(OverflowError)),
                    den: try!((self.den as i32 / n2d1).checked_mul(other.den as i32 / n1d2).ok_or(OverflowError)) as u32,
                }.check_overflow()
            },
        }
    }
    #[inline]
    pub fn div(&self, other: &Rational) -> Result<Rational, OverflowError> {
        self.mul(&try!(other.recip()))
    }
    pub fn add(&self, other: &Rational) -> Result<Rational, OverflowError> {
        let dgcd = gcd(self.den as i32, other.den as i32) as u32;
        let a = self.den / dgcd;
        let b = other.den / dgcd;
        let denom = try!(self.den.checked_mul(b).ok_or(OverflowError));
        // denom / self.den = b
        // denom / other.den = a
        Rational {
            num: self.num * b as i32 + other.num * a as i32,
            den: denom,
        }.check_overflow()
    }
    #[inline]
    pub fn sub(&self, other: &Rational) -> Result<Rational, OverflowError> {
        self.add(&other.negate())
    }
}

impl Ord for Rational {
    fn cmp(&self, other: &Rational) -> cmp::Ordering {
        if self.is_negative() != other.is_negative() {
            return self.num.cmp(&other.num)
        }
        if self.is_negative() {
            return self.negate().cmp(&other.negate()).reverse()
        }
        match (self.num.checked_mul(other.den as i32), (self.den as i32).checked_mul(other.num)) {
            (Some(a), Some(b)) => a.cmp(&b),
            _ => {
                // integer overflow with direct comparison
                if self.den == other.den {
                    return self.num.cmp(&other.num)
                }
                if self.num == other.num {
                    return other.den.cmp(&self.den)
                }
                let (ai, af) = (self.num / self.den as i32, self.num % self.den as i32);
                let (bi, bf) = (other.num / other.den as i32, other.num % other.den as i32);
                if ai > bi {
                    cmp::Ordering::Greater
                } else if ai < bi {
                    cmp::Ordering::Less
                } else { // partial fraction comparison
                    (Rational { num: other.den as i32, den: bf as u32 }).cmp(&Rational { num: self.den as i32, den: af as u32 })
                }
            }
        }
    }
}

impl PartialOrd for Rational {
    fn partial_cmp(&self, other: &Rational) -> Option<cmp::Ordering> {
        Some(self.cmp(other))
    }
}

pub trait AsFloat {
    fn as_float(&self) -> f64;
}

impl AsFloat for f64 {
    fn as_float(&self) -> f64 {
        *self
    }
}

impl AsFloat for Rational {
    fn as_float(&self) -> f64 {
        self.num as f64 / self.den as f64
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cmp;
    use std::cmp::Ordering;
    use std::fmt;
    use std::fmt::{Write, Display};
    
    macro_rules! rat {
        ( $num:tt / $den:tt ) => (Rational::new($num, $den).unwrap())
    }

    #[test]
    fn test_new_reduce() {
        assert_eq!(rat!(i32::min_value() / i32::min_value()), rat!(1 / 1));
        assert_eq!(rat!(i32::max_value() / i32::max_value()), rat!(1 / 1));
        assert_eq!(rat!(6 / 4), rat!(-3 / -2));
        assert_eq!(rat!(16 / 32), Rational { num: 1, den: 2 });
    }

    #[test]
    fn test_integer() {
        let nums = [i32::min_value(), i32::max_value(), -25, -5, -1, 0, 1, 5, 25];
        for m in nums.into_iter() {
            let n = *m;
            assert_eq!(Rational::new(n, 1), Rational::from_integer(n));
            if n != i32::min_value() {
                assert!(Rational::from_integer(n).unwrap().is_integer());
            } else {
                assert_eq!(Rational::from_integer(n), Err(OverflowError));
            }
        }
    }

    #[test]
    fn test_pow() {
        assert_eq!(rat!(3 / 2).pow(16), Rational::new(43046721, 65536));
        assert_eq!(rat!(3 / 2).pow(-16), Rational::new(65536, 43046721));
        assert_eq!(rat!(26 / 72).pow(200), Err(OverflowError));
        assert_eq!(rat!(26 / 72).pow(-200), Err(OverflowError));
    }

    #[test]
    fn test_cmp() {
        let tests = (vec![
            rat!(2147483645 / 2147483647),
            rat!(1073741823 / 1073741824),
            rat!(2147483644 / 2147483645),
            rat!(2147483645 / 2147483646),
            rat!(2147483646 / 2147483647),
            rat!(2147483647 / 2147483646),
        ]);
        fn compare(a: Rational, b: Rational, c: Ordering) {
            assert_eq!(a.cmp(&b), c);
            assert_eq!(b.cmp(&a).reverse(), c);
            assert_eq!(a.negate().cmp(&b.negate()).reverse(), c);
            assert_eq!(b.negate().cmp(&a.negate()), c);
        }
        for (i, &a) in tests.iter().enumerate() {
            compare(a, a, Ordering::Equal);
            assert!(a == a);
            compare(-a, a, Ordering::Less);
            for &b in &tests[i + 1..] {
                compare(a, b, Ordering::Less);
                compare(a.recip().unwrap(), b.recip().unwrap(), Ordering::Greater);
            }
        }
    }

    #[test]
    #[should_panic]
    fn test_zero_denom() {
        rat!(i32::min_value(), 0);
    }

    #[test]
    fn test_display() {
        fn test_str(a: Rational, b: &str) -> () {
            let mut s = String::new();
            write!(s, "{}", a);
            assert_eq!(s, b)
        }
        test_str(rat!(1 / 1), "1");
        test_str(rat!(5 / 1), "5");
        test_str(rat!(5 / -1), "-5");
        test_str(rat!(-5 / 1), "-5");
        test_str(rat!(-5 / -1), "5");
        test_str(rat!(5 / 2), "5/2");
        test_str(rat!(5 / -2), "-5/2");
    }
}
