#[derive(Copy, Clone, Hash, Debug, PartialEq, Eq)]
pub struct Rational {
    num: i32,
    den: u32,
}

#[derive(Debug, PartialEq, Eq)]
struct OverflowError;

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

#[inline]
fn gcd(mut m: i32, mut n: i32) -> i32 {
    // Use Stein's algorithm
    if m == 0 || n == 0 { return (m | n).abs() }

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
        return ((1 << shift) as i32).abs()
    }

    // guaranteed to be positive now, rest like unsigned algorithm
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

    n << shift
}

impl Rational {
    #[inline]
    pub fn from_integer(i: i32) -> Rational {
        Rational {
            num: i,
            den: 1,
        }
    }
    pub fn new(num: i32, den: i32) -> Rational {
        if den == 0 {
            panic!("denominator = 0");
        }
        let positive_gcd = gcd(num, den);
        let gcd = if den > 0 { positive_gcd } else { -positive_gcd };
        Rational {
            num: num / gcd,
            den: (den / gcd) as u32, // guaranteed to be positive
        }
    }
    #[inline]
    pub fn recip(&self) -> Rational {
        if self.num > 0 {
            Rational {
                num: self.den as i32,
                den: self.num as u32,
            }
        } else {
            Rational {
                num: -(self.den as i32),
                den: (-self.num) as u32,
            }
        }
    }
    pub fn is_integer(&self) -> bool {
        self.den == 1
    }
    #[inline]
    fn pow_r(&self, exp: i32) -> Result<Rational, OverflowError> {
        if exp != 0 {
            if exp > 0 {
                Ok(Rational {
                    num: try!(checked_pow(self.num, exp as u32)),
                    den: try!(checked_pow(self.den as i32, exp as u32)) as u32,
                })
            } else {
                Ok(try!(self.pow_r(-exp)).recip())
            }
        } else {
            Ok(Rational::from_integer(1))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new_reduce() {
        assert_eq!(Rational::new(6, 4), Rational::new(-3, -2));
    }
}
