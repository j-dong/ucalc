#[derive(Copy, Clone, Hash, Debug, PartialEq, Eq)]
pub struct Rational {
    num: i32,
    den: u32,
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
    pub fn recip(&self) -> Result<Rational, OverflowError> {
        if self.num > 0 {
            Ok(Rational {
                num: self.den as i32,
                den: self.num as u32,
            })
        } else {
            Ok(Rational {
                num: -(self.den as i32),
                den: (-self.num) as u32,
            })
        }
    }
    pub fn is_integer(&self) -> bool {
        self.den == 1
    }
    #[inline]
    fn pow_r(&self, exp: i32) -> Result<Rational, OverflowError> {
        if exp != 0 {
            if exp > 0 {
                Rational {
                    num: try!(checked_pow(self.num, exp as u32)),
                    den: try!(checked_pow(self.den as i32, exp as u32)) as u32,
                }.check_overflow()
            } else {
                if exp != i32::min_value() {
                    try!(self.pow_r(-exp)).recip()
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
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new_reduce() {
        assert_eq!(Rational::new(i32::min_value(), i32::min_value()), Rational::new(1, 1));
        assert_eq!(Rational::new(i32::max_value(), i32::max_value()), Rational::new(1, 1));
        assert_eq!(Rational::new(6, 4), Rational::new(-3, -2));
        assert_eq!(Rational::new(16, 32), Ok(Rational { num: 1, den: 2 }));
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
    #[should_panic]
    fn test_zero_denom() {
        Rational::new(i32::min_value(), 0);
    }
}
