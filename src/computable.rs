use crate::Rational;
use crate::computable::approximation::Approximation;
use core::cmp::Ordering;
use num::{BigInt, BigUint, bigint::Sign};
use num::{One, Zero};
use std::cell::RefCell;
use std::ops::Deref;

mod approximation;
mod format;

pub type Precision = i32;

#[derive(Clone, Debug, PartialEq)]
enum Cache {
    Invalid,
    Valid((Precision, BigInt)),
}

use std::sync::Arc;
use std::sync::atomic::AtomicBool;

pub type Signal = Arc<AtomicBool>;

fn should_stop(signal: &Option<Signal>) -> bool {
    use std::sync::atomic::Ordering::*;
    signal.as_ref().is_some_and(|s| s.load(Relaxed))
}

/// Computable approximation of a Real number.
#[derive(Clone, Debug)]
pub struct Computable {
    internal: Box<Approximation>,
    cache: RefCell<Cache>,
    signal: Option<Signal>,
}

mod rationals {
    use crate::Rational;
    use std::sync::LazyLock;

    pub(super) static SHORT_9: LazyLock<Rational> =
        LazyLock::new(|| Rational::fraction(1, 9).unwrap());
    pub(super) static SHORT_24: LazyLock<Rational> =
        LazyLock::new(|| Rational::fraction(1, 24).unwrap());
    pub(super) static SHORT_80: LazyLock<Rational> =
        LazyLock::new(|| Rational::fraction(1, 80).unwrap());
}

mod signed {
    use num::One;
    use num::{BigInt, bigint::ToBigInt};
    use std::sync::LazyLock;

    pub(super) static MINUS_ONE: LazyLock<BigInt> =
        LazyLock::new(|| ToBigInt::to_bigint(&-1).unwrap());
    pub(super) static ONE: LazyLock<BigInt> = LazyLock::new(BigInt::one);
    pub(super) static TWO: LazyLock<BigInt> = LazyLock::new(|| ToBigInt::to_bigint(&2).unwrap());
    pub(super) static THREE: LazyLock<BigInt> = LazyLock::new(|| ToBigInt::to_bigint(&3).unwrap());
    pub(super) static FOUR: LazyLock<BigInt> = LazyLock::new(|| ToBigInt::to_bigint(&4).unwrap());
    pub(super) static FIVE: LazyLock<BigInt> = LazyLock::new(|| ToBigInt::to_bigint(&5).unwrap());
    pub(super) static SIX: LazyLock<BigInt> = LazyLock::new(|| ToBigInt::to_bigint(&6).unwrap());
    pub(super) static SEVEN: LazyLock<BigInt> = LazyLock::new(|| ToBigInt::to_bigint(&7).unwrap());
    pub(super) static EIGHT: LazyLock<BigInt> = LazyLock::new(|| ToBigInt::to_bigint(&8).unwrap());
    pub(super) static TWENTY_FOUR: LazyLock<BigInt> =
        LazyLock::new(|| ToBigInt::to_bigint(&24).unwrap());
    pub(super) static SIXTY_FOUR: LazyLock<BigInt> =
        LazyLock::new(|| ToBigInt::to_bigint(&64).unwrap());
    pub(super) static TWO_THREE_NINE: LazyLock<BigInt> =
        LazyLock::new(|| ToBigInt::to_bigint(&239).unwrap());
}

mod unsigned {
    use num::One;
    use num::{BigUint, bigint::ToBigUint};
    use std::sync::LazyLock;

    pub(super) static ONE: LazyLock<BigUint> = LazyLock::new(BigUint::one);
    pub(super) static TWO: LazyLock<BigUint> = LazyLock::new(|| ToBigUint::to_biguint(&2).unwrap());
    pub(super) static TEN: LazyLock<BigUint> =
        LazyLock::new(|| ToBigUint::to_biguint(&10).unwrap());
    pub(super) static FIVE: LazyLock<BigUint> =
        LazyLock::new(|| ToBigUint::to_biguint(&5).unwrap());
    pub(super) static SIX: LazyLock<BigUint> = LazyLock::new(|| ToBigUint::to_biguint(&6).unwrap());
}

impl Computable {
    /// Exactly one.
    pub fn one() -> Computable {
        Self {
            internal: Box::new(Approximation::Int(BigInt::one())),
            cache: RefCell::new(Cache::Invalid),
            signal: None,
        }
    }

    /// Approximate π, the ratio of a circle's circumference to its diameter.
    pub fn pi() -> Computable {
        let atan5 = Self::prescaled_atan(signed::FIVE.clone());
        let atan_239 = Self::prescaled_atan(signed::TWO_THREE_NINE.clone());
        let four = Self::integer(signed::FOUR.clone());
        let four_atan5 = Self::multiply(four, atan5);
        let neg = Self::negate(atan_239);
        let sum = Self::add(four_atan5, neg);
        let four = Self::integer(signed::FOUR.clone());
        Self::multiply(four, sum)
    }

    /// Any Rational.
    pub fn rational(r: Rational) -> Computable {
        Self {
            internal: Box::new(Approximation::Ratio(r)),
            cache: RefCell::new(Cache::Invalid),
            signal: None,
        }
    }
}

impl Computable {
    pub(crate) fn e(r: Rational) -> Self {
        let rational = Self::rational(r);
        Self::exp(rational)
    }

    /// Natural Exponential function, raise Euler's Number to this number.
    pub fn exp(self) -> Computable {
        let low_prec: Precision = -10;
        let rough_appr: BigInt = self.approx(low_prec);
        if rough_appr.sign() == Sign::Minus {
            return self.negate().exp().inverse();
        }
        if rough_appr > *signed::TWO {
            let square_root = self.shift_right(1).exp();
            square_root.square()
        } else {
            Self {
                internal: Box::new(Approximation::PrescaledExp(self)),
                cache: RefCell::new(Cache::Invalid),
                signal: None,
            }
        }
    }

    /// Calculate nearby multiple of pi.
    fn pi_multiple(&self) -> BigInt {
        let mut rough_appr = self.approx(-1);
        let mut multiple = rough_appr / signed::SIX.deref();

        loop {
            let adj = Self::pi()
                .multiply(Self::rational(Rational::from_bigint(multiple.clone())).negate());
            let sum = self.clone().add(adj);
            rough_appr = sum.approx(-1);
            multiple += &rough_appr / signed::SIX.deref();

            let abs_rough_appr = rough_appr.magnitude();
            if abs_rough_appr < unsigned::SIX.deref() {
                return multiple;
            }
        }
    }

    /// Cosine of this number.
    pub fn cos(self) -> Computable {
        let rough_appr = self.approx(-1);
        let abs_rough_appr = rough_appr.magnitude();

        if abs_rough_appr >= unsigned::SIX.deref() {
            let multiplier = Self::pi_multiple(&self);
            let low_bit = multiplier.bit(0);

            let adjustment =
                Self::pi().multiply(Self::rational(Rational::from_bigint(multiplier)).negate());
            if low_bit {
                self.add(adjustment).cos().negate()
            } else {
                self.add(adjustment).cos()
            }
        } else if abs_rough_appr >= unsigned::TWO.deref() {
            // Scale further with double angle formula
            let cos_half = self.shift_right(1).cos();
            cos_half.square().shift_left(1).add(Self::one().negate())
        } else {
            Self {
                internal: Box::new(Approximation::PrescaledCos(self)),
                cache: RefCell::new(Cache::Invalid),
                signal: None,
            }
        }
    }

    /// Sine of this number.
    pub fn sin(self) -> Computable {
        Self::pi().shift_right(1).add(self.negate()).cos()
    }

    /// Tangent of this number.
    pub fn tan(self) -> Computable {
        let c = self.clone().cos().inverse();
        self.sin().multiply(c)
    }

    fn ln2() -> Self {
        let prescaled_9 = Self::rational(rationals::SHORT_9.clone()).prescaled_ln();
        let prescaled_24 = Self::rational(rationals::SHORT_24.clone()).prescaled_ln();
        let prescaled_80 = Self::rational(rationals::SHORT_80.clone()).prescaled_ln();

        let ln2_1 = Self::integer(signed::SEVEN.clone()).multiply(prescaled_9);
        let ln2_2 = Self::integer(signed::TWO.clone()).multiply(prescaled_24);
        let ln2_3 = Self::integer(signed::THREE.clone()).multiply(prescaled_80);

        let neg_ln2_2 = ln2_2.negate();

        ln2_1.add(neg_ln2_2).add(ln2_3)
    }

    /// Natural logarithm of this number.
    pub fn ln(self) -> Computable {
        // Sixteenths, ie 8 == 0.5, 24 == 1.5
        let low_ln_limit = signed::EIGHT.deref();
        let high_ln_limit = signed::TWENTY_FOUR.deref();

        let low_prec = -4;
        let rough_appr = self.approx(low_prec);
        if rough_appr < BigInt::zero() {
            panic!("ArithmeticException");
        }
        if rough_appr <= *low_ln_limit {
            return self.inverse().ln().negate();
        }
        if rough_appr >= *high_ln_limit {
            // Sixteenths, ie 64 == 4.0
            let sixty_four = signed::SIXTY_FOUR.deref();

            if rough_appr <= *sixty_four {
                let quarter = self.sqrt().sqrt().ln();
                return quarter.shift_left(2);
            } else {
                let extra_bits: i32 = (rough_appr.bits() - 3).try_into().expect(
                    "Approximation should have few enough bits to fit in a 32-bit signed integer",
                );
                let scaled_result = self.shift_right(extra_bits).ln();
                let extra: BigInt = extra_bits.into();
                return scaled_result.add(Self::integer(extra).multiply(Self::ln2()));
            }
        }

        let minus_one = Self::integer(signed::MINUS_ONE.clone());
        let fraction = Self::add(self, minus_one);
        Self::prescaled_ln(fraction)
    }

    fn prescaled_ln(self) -> Self {
        Self {
            internal: Box::new(Approximation::PrescaledLn(self)),
            cache: RefCell::new(Cache::Invalid),
            signal: None,
        }
    }

    pub(crate) fn sqrt_rational(r: Rational) -> Self {
        let rational = Self::rational(r);
        Self::sqrt(rational)
    }

    /// Square root of this number.
    pub fn sqrt(self) -> Computable {
        Self {
            internal: Box::new(Approximation::Sqrt(self)),
            cache: RefCell::new(Cache::Invalid),
            signal: None,
        }
    }

    fn prescaled_atan(n: BigInt) -> Self {
        Self {
            internal: Box::new(Approximation::IntegralAtan(n)),
            cache: RefCell::new(Cache::Invalid),
            signal: None,
        }
    }

    /// Negate this number.
    pub fn negate(self) -> Computable {
        Self {
            internal: Box::new(Approximation::Negate(self)),
            cache: RefCell::new(Cache::Invalid),
            signal: None,
        }
    }

    /// Multiplicative inverse of this number.
    pub fn inverse(self) -> Computable {
        Self {
            internal: Box::new(Approximation::Inverse(self)),
            cache: RefCell::new(Cache::Invalid),
            signal: None,
        }
    }

    fn shift_left(self, n: i32) -> Self {
        Self {
            internal: Box::new(Approximation::Offset(self, n)),
            cache: RefCell::new(Cache::Invalid),
            signal: None,
        }
    }

    fn shift_right(self, n: i32) -> Self {
        Self {
            internal: Box::new(Approximation::Offset(self, -n)),
            cache: RefCell::new(Cache::Invalid),
            signal: None,
        }
    }

    /// Square of this number.
    pub fn square(self) -> Self {
        Self {
            internal: Box::new(Approximation::Square(self)),
            cache: RefCell::new(Cache::Invalid),
            signal: None,
        }
    }

    /// Multiply this number by some other number.
    pub fn multiply(self, other: Computable) -> Computable {
        Self {
            internal: Box::new(Approximation::Multiply(self, other)),
            cache: RefCell::new(Cache::Invalid),
            signal: None,
        }
    }

    /// Add some other number to this number.
    #[allow(clippy::should_implement_trait)]
    pub fn add(self, other: Computable) -> Computable {
        Self {
            internal: Box::new(Approximation::Add(self, other)),
            cache: RefCell::new(Cache::Invalid),
            signal: None,
        }
    }

    pub(crate) fn integer(n: BigInt) -> Self {
        Self {
            internal: Box::new(Approximation::Int(n)),
            cache: RefCell::new(Cache::Invalid),
            signal: None,
        }
    }

    pub fn abort(&mut self, s: Signal) {
        self.signal = Some(s);
    }

    /// An approximation of this Computable scaled to a specific precision
    ///
    /// The approximation is scaled (thus, a larger value for more negative p)
    /// and should be accurate to within +/- 1 at the scale provided.
    ///
    /// Example: 0.875 is between 0 and 1 with zero bits of extra precision
    /// ```
    /// use realistic::{Rational,Computable};
    /// use num::{Zero,One};
    /// use num::bigint::{BigInt,ToBigInt};
    /// let n = Rational::fraction(7, 8).unwrap();
    /// let comp = Computable::rational(n);
    /// assert!((BigInt::zero() ..= BigInt::one()).contains(&comp.approx(0)));
    /// ```
    ///
    /// Example: π * 2³ is a bit more than 25 but less than 26
    /// ```
    /// use realistic::{Rational,Computable};
    /// use num::{Zero,One};
    /// use num::bigint::{BigInt,ToBigInt};
    /// let pi = Computable::pi();
    /// let between_25_26 = (ToBigInt::to_bigint(&25).unwrap() ..= ToBigInt::to_bigint(&26).unwrap());
    /// assert!(between_25_26.contains(&pi.approx(-3)));
    /// ```
    pub fn approx(&self, p: Precision) -> BigInt {
        self.approx_signal(&self.signal, p)
    }

    /// Like `approx` but specifying an atomic abort/ stop signal.
    pub fn approx_signal(&self, signal: &Option<Signal>, p: Precision) -> BigInt {
        // Check precision is OK?

        if let Cache::Valid((cache_prec, cache_appr)) = self.cache.clone().into_inner() {
            if p >= cache_prec {
                return scale(cache_appr, cache_prec - p);
            }
        }
        let result = self.internal.approximate(signal, p);
        self.cache.replace(Cache::Valid((p, result.clone())));
        result
    }

    pub fn sign(&self) -> Sign {
        if let Cache::Valid((_prec, cache_appr)) = self.cache.clone().into_inner() {
            let sign = cache_appr.sign();
            if sign != Sign::NoSign {
                return sign;
            }
        }
        let mut sign = Sign::NoSign;
        let mut p = 0;
        while p > -2000 && sign == Sign::NoSign {
            let appr = self.approx(p);
            p -= 10;
            sign = appr.sign();
        }
        sign
    }

    fn cached(&self) -> Option<(Precision, BigInt)> {
        if let Cache::Valid((cache_prec, cache_appr)) = self.cache.clone().into_inner() {
            Some((cache_prec, cache_appr))
        } else {
            None
        }
    }

    /// Do not call this function if `self` and `other` may be the same.
    pub fn compare_to(&self, other: &Self) -> Ordering {
        let mut tolerance = -20;
        while tolerance > Precision::MIN {
            let order = self.compare_absolute(other, tolerance);
            if order != Ordering::Equal {
                return order;
            }
            tolerance *= 2;
        }
        panic!("Apparently called Computable::compare_to on equal values");
    }

    /// Compare two values to a specified tolerance (more negative numbers are more precise).
    pub fn compare_absolute(&self, other: &Self, tolerance: Precision) -> Ordering {
        let needed = tolerance - 1;
        let this = self.approx(needed);
        let alt = other.approx(needed);
        let max = alt.clone() + signed::ONE.deref();
        let min = alt.clone() - signed::ONE.deref();
        if this > max {
            Ordering::Greater
        } else if this < min {
            Ordering::Less
        } else {
            Ordering::Equal
        }
    }

    /// Most Significant Digit (Bit) ?
    /// May panic or give incorrect answers if not yet discovered.
    fn known_msd(&self) -> Precision {
        if let Some((prec, appr)) = self.cached() {
            let length = appr.magnitude().bits() as Precision;
            prec + length - 1
        } else {
            panic!("Expected valid cache state for known MSD but it's invalid")
        }
    }

    /// MSD - or perhaps None if as yet undiscovered and less than p.
    fn msd(&self, p: Precision) -> Option<Precision> {
        let cache = self.cached();
        let mut try_once = false;

        if cache.is_none() {
            try_once = true;
        } else if let Some((_prec, appr)) = cache {
            let one = signed::ONE.deref();
            let minus_one = signed::MINUS_ONE.deref();

            if appr > *minus_one && appr < *one {
                try_once = true;
            }
        }

        if try_once {
            let appr = self.approx(p - 1);
            if appr.magnitude() < &BigUint::one() {
                return None;
            }
        }

        Some(self.known_msd())
    }

    const STOP_PRECISION: Precision = Precision::MIN / 3;

    /// MSD iteratively: 0, -16, -40, -76 etc. or p if that's lower.
    /// You can choose p to avoid unnecessary work.
    pub(super) fn iter_msd_stop(&self, p: Precision) -> Option<Precision> {
        let mut prec = 0;

        loop {
            let msd = self.msd(prec);
            if msd.is_some() {
                return msd;
            }
            prec = (prec * 3) / 2 - 16;
            if prec <= p {
                break;
            }
            if should_stop(&self.signal) {
                break;
            }
        }
        self.msd(p)
    }

    /// MSD but iteratively without a guess as to precision.
    pub(super) fn iter_msd(&self) -> Precision {
        self.iter_msd_stop(Self::STOP_PRECISION)
            .unwrap_or(Self::STOP_PRECISION)
    }
}

fn shift(n: BigInt, p: Precision) -> BigInt {
    match 0.cmp(&p) {
        Ordering::Greater => n >> -p,
        Ordering::Equal => n,
        Ordering::Less => n << p,
    }
}

/// Scale n by p bits, rounding if this makes n smaller.
/// e.g. scale(10, 2) == 40
///      scale(10, -2) == 3
fn scale(n: BigInt, p: Precision) -> BigInt {
    if p >= 0 {
        n << p
    } else {
        let adj = shift(n, p + 1) + signed::ONE.deref();
        adj >> 1
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn compare() {
        let six: BigInt = "6".parse().unwrap();
        let five: BigInt = "5".parse().unwrap();
        let four: BigInt = "4".parse().unwrap();
        let six = Computable::integer(six.clone());
        let five = Computable::integer(five.clone());
        let four = Computable::integer(four.clone());

        assert_eq!(six.compare_to(&five), Ordering::Greater);
        assert_eq!(five.compare_to(&six), Ordering::Less);
        assert_eq!(four.compare_to(&six), Ordering::Less);
    }

    #[test]
    fn bigger() {
        let six: BigInt = "6".parse().unwrap();
        let five: BigInt = "5".parse().unwrap();
        let four: BigInt = "4".parse().unwrap();
        let a = Computable::integer(six.clone());
        let b = Computable::integer(five.clone());
        assert_eq!(a.compare_absolute(&b, 0), Ordering::Greater);
        let c = Computable::integer(four.clone());
        assert_eq!(c.compare_absolute(&a, 0), Ordering::Less);
        assert_eq!(b.compare_absolute(&b, 0), Ordering::Equal);
    }

    #[test]
    fn shifted() {
        let one = BigInt::one();
        let two = &one + &one;
        assert_eq!(one, shift(two, -1));
    }

    #[test]
    fn prec() {
        let nine: BigInt = "9".parse().unwrap();
        let five: BigInt = "5".parse().unwrap();
        let two: BigInt = "2".parse().unwrap();
        let one = BigInt::one();
        let a = Computable::integer(nine.clone());
        assert_eq!(nine, a.approx(0));
        assert_eq!(five, a.approx(1));
        assert_eq!(two, a.approx(2));
        assert_eq!(one, a.approx(3));
        assert_eq!(Cache::Valid((0, nine)), a.cache.into_inner());
    }

    #[test]
    fn prec_pi() {
        let three: BigInt = "3".parse().unwrap();
        let six: BigInt = "6".parse().unwrap();
        let thirteen: BigInt = "13".parse().unwrap();
        let four_zero_two: BigInt = "402".parse().unwrap();
        let a = Computable::pi();
        assert_eq!(four_zero_two, a.approx(-7));
        assert_eq!(three, a.approx(0));
        assert_eq!(six, a.approx(-1));
        assert_eq!(thirteen, a.approx(-2));
        assert_eq!(Cache::Valid((-7, four_zero_two)), a.cache.into_inner());
    }

    #[test]
    fn prec_atan_5() {
        let five: BigInt = "5".parse().unwrap();
        let atan_5 = Computable::prescaled_atan(five);
        let two_zero_two: BigInt = "202".parse().unwrap();
        assert_eq!(two_zero_two, atan_5.approx(-10));
        let at_twenty: BigInt = "206984".parse().unwrap();
        assert_eq!(at_twenty, atan_5.approx(-20));
    }

    #[test]
    fn prec_atan_239() {
        let two_three_nine: BigInt = "239".parse().unwrap();
        let atan_239 = Computable::prescaled_atan(two_three_nine);
        let four: BigInt = "4".parse().unwrap();
        assert_eq!(four, atan_239.approx(-10));
        let at_twenty: BigInt = "4387".parse().unwrap();
        assert_eq!(at_twenty, atan_239.approx(-20));
    }

    #[test]
    fn msd() {
        let one: BigInt = "1".parse().unwrap();
        let a = Computable::integer(one.clone());
        assert_eq!(Some(0), a.msd(-4));
        let three: BigInt = "3".parse().unwrap();
        let d = Computable::integer(three.clone());
        assert_eq!(Some(1), d.msd(-4));
        let five: BigInt = "5".parse().unwrap();
        let e = Computable::integer(five.clone());
        assert_eq!(Some(2), e.msd(-4));
        let seven: BigInt = "7".parse().unwrap();
        let f = Computable::integer(seven.clone());
        assert_eq!(Some(2), f.msd(-4));
        let eight: BigInt = "8".parse().unwrap();
        let g = Computable::integer(eight.clone());
        assert_eq!(Some(3), g.msd(-4));
    }

    #[test]
    fn iter_msd() {
        let one = Computable::one();
        assert_eq!(one.iter_msd(), 0);
        let pi = Computable::pi();
        assert_eq!(pi.iter_msd(), 1);
        let five = Rational::new(5);
        let e = Computable::e(five);
        assert_eq!(e.iter_msd(), 7);
    }

    #[test]
    fn negate() {
        let fifteen: BigInt = "15".parse().unwrap();
        let a = Computable::integer(fifteen.clone());
        let b = Computable::negate(a);
        let answer: BigInt = "-8".parse().unwrap();
        assert_eq!(answer, b.approx(1));
    }

    #[test]
    fn multiply() {
        let four: BigInt = "4".parse().unwrap();
        let five: BigInt = "5".parse().unwrap();
        let a = Computable::integer(four);
        let b = Computable::prescaled_atan(five);
        let m = Computable::multiply(a, b);
        let answer: BigInt = "809".parse().unwrap();
        assert_eq!(answer, m.approx(-10));
    }

    #[test]
    fn multiply_opposite() {
        let four: BigInt = "4".parse().unwrap();
        let five: BigInt = "5".parse().unwrap();
        let a = Computable::integer(four);
        let b = Computable::prescaled_atan(five);
        let m = Computable::multiply(b, a);
        let answer: BigInt = "809".parse().unwrap();
        assert_eq!(answer, m.approx(-10));
    }

    #[test]
    fn rational() {
        let sixth: Rational = "1/6".parse().unwrap();
        let c = Computable::rational(sixth);
        let zero = BigInt::zero();
        let one = BigInt::one();
        let ten: BigInt = "10".parse().unwrap();
        let eighty_five: BigInt = "85".parse().unwrap();
        assert_eq!(zero, c.approx(0));
        assert_eq!(zero, c.approx(-1));
        assert_eq!(zero, c.approx(-2));
        assert_eq!(one, c.approx(-3));
        assert_eq!(ten, c.approx(-6));
        assert_eq!(eighty_five, c.approx(-9));
    }

    #[test]
    fn scaled_ln1() {
        let zero = Computable::integer(BigInt::zero());
        let ln = Computable {
            internal: Box::new(Approximation::PrescaledLn(zero)),
            cache: RefCell::new(Cache::Invalid),
            signal: None,
        };
        let zero = BigInt::zero();
        assert_eq!(zero, ln.approx(100));
    }

    #[test]
    fn scaled_ln1_4() {
        let zero_4: Rational = "0.4".parse().unwrap();
        let rational = Computable::rational(zero_4);
        let ln = Computable {
            internal: Box::new(Approximation::PrescaledLn(rational)),
            cache: RefCell::new(Cache::Invalid),
            signal: None,
        };
        let five: BigInt = "5".parse().unwrap();
        assert_eq!(five, ln.approx(-4));
    }

    #[test]
    fn ln() {
        let five: BigInt = "5".parse().unwrap();
        let integer = Computable::integer(five);
        let ln = Computable::ln(integer);
        let correct: BigInt = "1769595698905".parse().unwrap();
        assert_eq!(ln.approx(-40), correct);
    }

    #[test]
    fn cos_zero() {
        let zero = Computable::rational(Rational::zero());
        let cos = zero.cos();
        let correct: BigInt = "4294967296".parse().unwrap();
        assert_eq!(cos.approx(-32), correct);
    }

    #[test]
    fn cos_one() {
        let one = Computable::one();
        let cos = one.cos();
        let correct: BigInt = "2320580734".parse().unwrap();
        assert_eq!(cos.approx(-32), correct);
    }

    #[test]
    fn ln_sqrt_pi() {
        let pi = Computable::pi();
        let sqrt = Computable::sqrt(pi);
        let ln = Computable::ln(sqrt);
        let correct: BigInt = "629321910077".parse().unwrap();
        assert_eq!(ln.approx(-40), correct);
    }

    #[test]
    fn add() {
        let three: BigInt = "3".parse().unwrap();
        let five: BigInt = "5".parse().unwrap();
        let a = Computable::integer(three);
        let b = Computable::integer(five);
        let c = Computable::add(a, b);
        let answer: BigInt = "256".parse().unwrap();
        assert_eq!(answer, c.approx(-5));
    }

    #[test]
    fn scale_up() {
        let ten: BigInt = "10".parse().unwrap();
        let three: BigInt = "3".parse().unwrap();
        assert_eq!(ten, scale(ten.clone(), 0));
        let a = scale(ten.clone(), -2);
        assert_eq!(three, a);
        let forty: BigInt = "40".parse().unwrap();
        let b = scale(ten.clone(), 2);
        assert_eq!(forty, b);
    }
}
