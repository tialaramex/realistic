use lazy_static::lazy_static;
use num_bigint::Sign::{self, *};
use num_bigint::{BigUint, ToBigUint};
use num_traits::{Zero, One};

#[derive(Clone, Debug)]
pub struct ParseBRError();

#[derive(Clone, Debug)]
pub struct BoundedRational {
    sign: Sign,
    numerator: BigUint,
    denominator: BigUint,
}

impl BoundedRational {
    pub fn zero() -> Self {
        Self {
            sign: NoSign,
            numerator: Zero::zero(),
            denominator: One::one(),
        }
    }

    pub fn new(n: u64) -> Self {
        Self {
            sign: Plus,
            numerator: ToBigUint::to_biguint(&n).unwrap(),
            denominator: One::one(),
        }
    }

    pub fn fraction(n: u64, d: u64) -> Self {
        Self {
            sign: Plus,
            numerator: ToBigUint::to_biguint(&n).unwrap(),
            denominator: ToBigUint::to_biguint(&d).unwrap(),
        }
    }

    fn maybe_reduce(self) -> Self {
        /* for now, always */
        self.reduce()
    }

    fn reduce(self) -> Self {
        if self.denominator == One::one() {
            self
        } else {
            let divisor = num::Integer::gcd(&self.numerator, &self.denominator);
            let numerator = self.numerator / &divisor;
            let denominator = self.denominator / &divisor;
            Self {
                sign: self.sign,
                numerator,
                denominator,
            }
        }
    }

    pub fn inverse(self) -> Self {
        Self {
            sign: self.sign,
            numerator: self.denominator,
            denominator: self.numerator,
        }
    }
}

impl BoundedRational {
    pub fn sign(&self) -> Sign {
        self.sign
    }
}

impl BoundedRational {
    const EXTRACT_SQUARE_MAX_OPT: u8 = 43;
    const EXTRACT_SQUARE_MAX_LEN: u64 = 5000;

    fn make_squares() -> Vec<(BigUint, BigUint)> {
        let mut v = Vec::new();
        v.push((
            ToBigUint::to_biguint(&2).unwrap(),
            ToBigUint::to_biguint(&4).unwrap(),
        ));
        v.push((
            ToBigUint::to_biguint(&3).unwrap(),
            ToBigUint::to_biguint(&9).unwrap(),
        ));
        v.push((
            ToBigUint::to_biguint(&5).unwrap(),
            ToBigUint::to_biguint(&25).unwrap(),
        ));
        v.push((
            ToBigUint::to_biguint(&7).unwrap(),
            ToBigUint::to_biguint(&49).unwrap(),
        ));
        v.push((
            ToBigUint::to_biguint(&11).unwrap(),
            ToBigUint::to_biguint(&121).unwrap(),
        ));
        v.push((
            ToBigUint::to_biguint(&13).unwrap(),
            ToBigUint::to_biguint(&169).unwrap(),
        ));
        v
    }

    fn extract_square(n: BigUint) -> (BigUint, BigUint) {
        lazy_static! {
            static ref SQUARES: Vec<(BigUint, BigUint)> = BoundedRational::make_squares();
        }

        let mut square = ToBigUint::to_biguint(&1).unwrap();
        let mut rest = n;
        if rest.bits() > Self::EXTRACT_SQUARE_MAX_LEN {
            return (square, rest);
        }
        for (p, s) in &*SQUARES {
            if &rest == &ToBigUint::to_biguint(&1).unwrap() {
                break;
            }
            while &rest % s == ToBigUint::to_biguint(&0).unwrap() {
                rest /= s;
                square *= p;
            }
        }

        (square, rest)
    }

    pub fn extract_square_reduced(self) -> (Self, Self) {
        if self.sign == NoSign {
            return (Self::zero(), Self::new(0));
        }
        let (nsquare, nrest) = Self::extract_square(self.numerator);
        let (dsquare, drest) = Self::extract_square(self.denominator);
        if self.sign == Minus {
            todo!("Didn't yet implement extract_square_reduced for negative rationals")
        } else {
            (
                Self {
                    sign: self.sign,
                    numerator: nsquare,
                    denominator: dsquare,
                },
                Self {
                    sign: self.sign,
                    numerator: nrest,
                    denominator: drest,
                },
            )
        }
    }

    pub fn extract_square_will_succeed(&self) -> bool {
        self.numerator.bits() < Self::EXTRACT_SQUARE_MAX_LEN
            && self.denominator.bits() < Self::EXTRACT_SQUARE_MAX_LEN
    }
}

use std::str::FromStr;

impl FromStr for BoundedRational {
    type Err = ParseBRError;

    fn from_str(s: &str) -> Result<Self, ParseBRError> {
        let mut sign: Sign = Plus;
        let s = match s.strip_prefix('-') {
            Some(s) => {
                sign = Minus;
                s
            }
            None => s,
        };
        if let Some((n, d)) = s.split_once('/') {
            let numerator= BigUint::parse_bytes(n.as_bytes(), 10).ok_or(ParseBRError {})?;
            if numerator.is_zero() {
                sign = NoSign;
            }
            Ok(Self {
                sign,
                numerator,
                denominator: BigUint::parse_bytes(d.as_bytes(), 10).ok_or(ParseBRError {})?,
            })
        } else {
            let numerator= BigUint::parse_bytes(s.as_bytes(), 10).ok_or(ParseBRError {})?;
            if numerator.is_zero() {
                sign = NoSign;
            }
            Ok(Self {
                sign,
                numerator,
                denominator: One::one(),
            })
        }
    }
}

/* TryFrom<f64> for BoundedRational see Java valueOf() */

use core::ops::*;
use std::cmp::Ordering;

impl Add for BoundedRational {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        let denominator = &self.denominator * &other.denominator;
        let a = self.numerator * other.denominator;
        let b = other.numerator * self.denominator;
        let (sign, numerator) = match (self.sign, other.sign) {
            (any, NoSign) => (any, a),
            (Plus, Plus) => (Plus, a + b),
            (Minus, Minus) => (Minus, a + b),
            (x, y) => match a.cmp(&b) {
                Ordering::Greater => (x, a - b),
                Ordering::Equal => {
                    return Self::zero();
                }
                Ordering::Less => (y, b - a),
            },
        };
        Self::maybe_reduce(Self {
            sign,
            numerator,
            denominator,
        })
    }
}

impl Neg for BoundedRational {
    type Output = Self;

    fn neg(self) -> Self {
        Self {
            sign: -self.sign,
            ..self
        }
    }
}

impl Sub for BoundedRational {
    type Output = Self;

    fn sub(self, other: Self) -> Self {
        self + -other
    }
}

impl Mul for BoundedRational {
    type Output = Self;

    fn mul(self, other: Self) -> Self {
        let sign = self.sign * other.sign;
        let numerator = self.numerator * other.numerator;
        let denominator = self.denominator * other.denominator;
        Self::maybe_reduce(Self {
            sign,
            numerator,
            denominator,
        })
    }
}

impl Div for BoundedRational {
    type Output = Self;

    fn div(self, other: Self) -> Self {
        let sign = self.sign * other.sign;
        let numerator = self.numerator * other.denominator;
        let denominator = self.denominator * other.numerator;
        Self::maybe_reduce(Self {
            sign,
            numerator,
            denominator,
        })
    }
}

impl BoundedRational {
    fn definitely_equal(&self, other: &Self) -> bool {
        if self.sign != other.sign {
            return false;
        }
        if self.denominator != other.denominator {
            return false;
        }
        self.numerator == other.numerator
    }
}

impl PartialEq for BoundedRational {
    fn eq(&self, other: &Self) -> bool {
        if self.sign != other.sign {
            return false;
        }
        if self.denominator == other.denominator {
            self.numerator == other.numerator
        } else {
            Self::definitely_equal(&self.clone().reduce(), &other.clone().reduce())
        }
    }
}

#[cfg(test)]
#[test]
/// See e.g. https://discussions.apple.com/thread/252474975
/// Apple calculator is not trustworthy if you are a programmer
fn parse() {
    let big: BoundedRational = "288230376151711743".parse().unwrap();
    let small: BoundedRational = "45".parse().unwrap();
    let expected: BoundedRational = "12970366926827028435".parse().unwrap();
    assert_eq!(big * small, expected);
}

#[test]
fn parse_fractions() {
    let third: BoundedRational = "1/3".parse().unwrap();
    let minus_four: BoundedRational = "-4".parse().unwrap();
    let twelve: BoundedRational = "12/20".parse().unwrap();
    let answer = third + minus_four * twelve;
    let expected: BoundedRational = "-31/15".parse().unwrap();
    assert_eq!(answer, expected);
}

#[test]
fn signs() {
    let half = BoundedRational::fraction(4, 8);
    let one = BoundedRational::new(1);
    let minus_half = half - one;
    let two = BoundedRational::new(2);
    let zero = BoundedRational::zero();
    let minus_two = zero - two;
    let i2 = minus_two.inverse();
    assert_eq!(i2, minus_half);
}

#[test]
fn half_plus_one_times_two() {
    let two = BoundedRational::new(2);
    let half = two.inverse();
    let one = BoundedRational::new(1);
    let two = BoundedRational::new(2);
    let three = BoundedRational::new(3);
    let sum = half + one;
    assert_eq!(sum * two, three);
}

#[test]
fn three_divided_by_six() {
    let three = BoundedRational::new(3);
    let six = BoundedRational::new(6);
    let half = BoundedRational::fraction(1, 2);
    assert_eq!(three / six, half);
}

#[test]
fn one_plus_two() {
    let one = BoundedRational::new(1);
    let two = BoundedRational::new(2);
    let three = BoundedRational::new(3);
    assert_eq!(one + two, three);
}

#[test]
fn two_minus_one() {
    let two = BoundedRational::new(2);
    let one = BoundedRational::new(1);
    assert_eq!(two - one, BoundedRational::new(1));
}

#[test]
fn two_times_three() {
    let two = BoundedRational::new(2);
    let three = BoundedRational::new(3);
    assert_eq!(two * three, BoundedRational::new(6));
}
