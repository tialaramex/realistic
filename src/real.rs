use crate::computable::Precision;
use crate::{Computable, Problem, Rational};
use num::bigint::{BigInt, BigUint, Sign};
use std::cmp::Ordering;

mod convert;
#[cfg(test)]
mod normal_reference;
mod test;

#[derive(Clone, Debug)]
enum Class {
    One,             // Exactly one
    Pi,              // Exactly pi
    Sqrt(Rational),  // Square root of some positive integer without an integer square root
    Exp(Rational),   // Rational is never zero
    Ln(Rational),    // Rational > 1
    Log10(Rational), // Rational > 1 and never a multiple of ten
    SinPi(Rational), // 0 < Rational < 1/2 also never 1/6 or 1/4 or 1/3
    TanPi(Rational), // 0 < Rational < 1/2 also never 1/6 or 1/4 or 1/3
    Irrational,
}

use Class::*;

// We can't tell whether an Irrational value is ever equal to anything
impl PartialEq for Class {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (One, One) => true,
            (Pi, Pi) => true,
            (Sqrt(r), Sqrt(s)) => r == s,
            (Exp(r), Exp(s)) => r == s,
            (Ln(r), Ln(s)) => r == s,
            (Log10(r), Log10(s)) => r == s,
            (SinPi(r), SinPi(s)) => r == s,
            (TanPi(r), TanPi(s)) => r == s,
            (_, _) => false,
        }
    }
}

impl Class {
    // Could treat Exp specially for large negative exponents
    fn is_non_zero(&self) -> bool {
        true
    }

    // Any logarithm can be added
    fn is_ln(&self) -> bool {
        matches!(self, Ln(_))
    }

    fn make_exp(br: Rational) -> (Class, Computable) {
        if br == *rationals::ZERO {
            (One, Computable::one())
        } else {
            (Exp(br.clone()), Computable::e(br))
        }
    }
}

mod rationals {
    use crate::Rational;
    use std::sync::LazyLock;

    pub(super) static HALF: LazyLock<Rational> =
        LazyLock::new(|| Rational::fraction(1, 2).unwrap());
    pub(super) static ONE: LazyLock<Rational> = LazyLock::new(|| Rational::new(1));
    pub(super) static ZERO: LazyLock<Rational> = LazyLock::new(Rational::zero);
    pub(super) static TEN: LazyLock<Rational> = LazyLock::new(|| Rational::new(10));
}

mod signed {
    use num::{BigInt, bigint::ToBigInt};
    use std::sync::LazyLock;

    pub(super) static ONE: LazyLock<BigInt> = LazyLock::new(|| ToBigInt::to_bigint(&1).unwrap());
}

mod unsigned {
    use num::{BigUint, bigint::ToBigUint};
    use std::sync::LazyLock;

    pub(super) static ONE: LazyLock<BigUint> = LazyLock::new(|| ToBigUint::to_biguint(&1).unwrap());
    pub(super) static TWO: LazyLock<BigUint> = LazyLock::new(|| ToBigUint::to_biguint(&2).unwrap());
    pub(super) static THREE: LazyLock<BigUint> =
        LazyLock::new(|| ToBigUint::to_biguint(&3).unwrap());
    pub(super) static FOUR: LazyLock<BigUint> =
        LazyLock::new(|| ToBigUint::to_biguint(&4).unwrap());
    pub(super) static SIX: LazyLock<BigUint> = LazyLock::new(|| ToBigUint::to_biguint(&6).unwrap());
}

use std::sync::LazyLock;
static LN10: LazyLock<Class> = LazyLock::new(|| Ln(Rational::new(10)));

/// Largest |x| for which we evaluate Φ(x) / Φ⁻¹. Beyond this the erf series needs
/// impractically many terms and Φ is within ~10⁻²³ of 0 or 1.
const PNORM_MAX_ABS: f64 = 10.0;
/// Tolerance (in bits) for the exact CR comparisons guarding qnorm's domain.
const DEFAULT_COMPARE_TOLERANCE: Precision = -1000;

// Φ(10) and Φ(−10) = 1 − Φ(10), the probabilities at the ±10 cap. Φ⁻¹(p) is in
// range exactly when p lies strictly inside (cap_lo, cap_hi).
fn pnorm_cap_hi() -> Computable {
    Computable::integer(BigInt::from(10)).pnorm()
}
fn pnorm_cap_lo() -> Computable {
    Computable::one().add(pnorm_cap_hi().negate())
}

/// Acklam's rational approximation to Φ⁻¹(p) (|error| ≲ 1.2e-9). Used only to seed
/// the exact CR inversion, so this accuracy is ample.
// Constants are Acklam's published 16-figure values, kept verbatim even though the
// last figure is below f64's resolution.
#[allow(clippy::excessive_precision)]
fn qnorm_approx(p: f64) -> f64 {
    const A: [f64; 6] = [
        -3.969683028665376e+01,
        2.209460984245205e+02,
        -2.759285104469687e+02,
        1.383577518672690e+02,
        -3.066479806614716e+01,
        2.506628277459239e+00,
    ];
    const B: [f64; 5] = [
        -5.447609879822406e+01,
        1.615858368580409e+02,
        -1.556989798598866e+02,
        6.680131188771972e+01,
        -1.328068155288572e+01,
    ];
    const C: [f64; 6] = [
        -7.784894002430293e-03,
        -3.223964580411365e-01,
        -2.400758277161838e+00,
        -2.549732539343734e+00,
        4.374664141464968e+00,
        2.938163982698783e+00,
    ];
    const D: [f64; 4] = [
        7.784695709041462e-03,
        3.224671290700398e-01,
        2.445134137142996e+00,
        3.754408661907416e+00,
    ];
    const P_LOW: f64 = 0.02425;
    if p < P_LOW {
        let q = (-2.0 * p.ln()).sqrt();
        (((((C[0] * q + C[1]) * q + C[2]) * q + C[3]) * q + C[4]) * q + C[5])
            / ((((D[0] * q + D[1]) * q + D[2]) * q + D[3]) * q + 1.0)
    } else if p <= 1.0 - P_LOW {
        let q = p - 0.5;
        let r = q * q;
        (((((A[0] * r + A[1]) * r + A[2]) * r + A[3]) * r + A[4]) * r + A[5]) * q
            / (((((B[0] * r + B[1]) * r + B[2]) * r + B[3]) * r + B[4]) * r + 1.0)
    } else {
        let q = (-2.0 * (1.0 - p).ln()).sqrt();
        -(((((C[0] * q + C[1]) * q + C[2]) * q + C[3]) * q + C[4]) * q + C[5])
            / ((((D[0] * q + D[1]) * q + D[2]) * q + D[3]) * q + 1.0)
    }
}

use std::sync::Arc;
use std::sync::atomic::AtomicBool;

pub type Signal = Arc<AtomicBool>;

/// (More) Real numbers
///
/// This type is functionally the product of a [`Computable`] number
/// and a [`Rational`].
///
/// # Examples
///
/// Even a normal rational can be parsed as a Real
/// ```
/// use realistic::{Real, Rational};
/// let half: Real = "0.5".parse().unwrap();
/// assert_eq!(half, Rational::fraction(1, 2).unwrap());
/// ```
///
/// Simple arithmetic
/// ```
/// use realistic::Real;
/// let two_pi = Real::pi() + Real::pi();
/// let four: Real = "4".parse().unwrap();
/// let four_pi = four * Real::pi();
/// let answer = (four_pi / two_pi).unwrap();
/// let two = realistic::Rational::new(2);
/// assert_eq!(answer, Real::new(two));
/// ```
///
/// Conversion
/// ```
/// use realistic::{Real, Rational};
/// let nine: Real = 9.into();
/// let three = Rational::new(3);
/// let answer = nine.sqrt().unwrap();
/// assert_eq!(answer, three);
/// ```
#[derive(Clone, Debug)]
pub struct Real {
    rational: Rational,
    class: Class,
    computable: Computable,
    signal: Option<Signal>,
}

impl Real {
    /// Provide an atomic flag to signal early abort of calculations.
    /// The provided flag can be used e.g. from another execution thread.
    /// Aborted calculations may have incorrect results.
    pub fn abort(&mut self, s: Signal) {
        self.signal = Some(s.clone());
        self.computable.abort(s);
    }

    /// Zero, the additive identity.
    pub fn zero() -> Real {
        Self {
            rational: Rational::zero(),
            class: One,
            computable: Computable::one(),
            signal: None,
        }
    }

    /// The specified [`Rational`] as a Real.
    pub fn new(rational: Rational) -> Real {
        Self {
            rational,
            class: One,
            computable: Computable::one(),
            signal: None,
        }
    }

    /// π, the ratio of a circle's circumference to its diameter.
    pub fn pi() -> Real {
        Self {
            rational: Rational::one(),
            class: Pi,
            computable: Computable::pi(),
            signal: None,
        }
    }

    /// e, Euler's number and the base of the natural logarithm function.
    pub fn e() -> Real {
        let one = Rational::one();
        Self {
            rational: one.clone(),
            class: Exp(one.clone()),
            computable: Computable::e(one),
            signal: None,
        }
    }
}

// Tan(r) is a repeating shape
// returns whether to negate, and the (if necessary reflected) fraction
// 0 < r < 0.5
// Never actually used for exact zero or half
fn tan_curve(r: Rational) -> (bool, Rational) {
    let mut s = r.fract();
    let mut flip = false;
    if s.sign() == Sign::Minus {
        flip = true;
        s = s.neg();
    }
    if s > *rationals::HALF {
        (!flip, Rational::one() - s)
    } else {
        (flip, s)
    }
}

// Sin(r) is a single curve, then reflected, then both halves negated
// returns whether to negate, and the (if necessary reflected) fraction
// 0 < r < 0.5
// Never actually used for exact zero or half
fn curve(r: Rational) -> (bool, Rational) {
    let whole = r.shifted_big_integer(0);
    let mut s = r.fract();
    if s.sign() == Sign::Minus {
        s = s.neg();
    }
    if s > *rationals::HALF {
        s = Rational::one() - s;
    }
    (whole.bit(0), s)
}

impl Real {
    /// Is this Real exactly zero?
    pub fn definitely_zero(&self) -> bool {
        self.rational.sign() == Sign::NoSign
    }

    /// Are two Reals definitely unequal?
    pub fn definitely_not_equal(&self, other: &Self) -> bool {
        if self.rational.sign() == Sign::NoSign {
            return other.class.is_non_zero() && other.rational.sign() != Sign::NoSign;
        }
        if other.rational.sign() == Sign::NoSign {
            return self.class.is_non_zero() && self.rational.sign() != Sign::NoSign;
        }
        false
        /* ... TODO add more cases which definitely aren't equal */
    }

    /// Our best attempt to discern the [`Sign`] of this Real.
    /// This will be accurate for trivial Rationals and many but not all other cases.
    pub fn best_sign(&self) -> Sign {
        match &self.class {
            One | Pi | Sqrt(_) | Exp(_) | Ln(_) | Log10(_) | SinPi(_) | TanPi(_) => {
                self.rational.sign()
            }
            _ => match (self.rational.sign(), self.computable.sign()) {
                (Sign::NoSign, _) => Sign::NoSign,
                (_, Sign::NoSign) => Sign::NoSign,
                (Sign::Plus, Sign::Plus) => Sign::Plus,
                (Sign::Plus, Sign::Minus) => Sign::Minus,
                (Sign::Minus, Sign::Plus) => Sign::Minus,
                (Sign::Minus, Sign::Minus) => Sign::Plus,
            },
        }
    }

    // Given a function which makes a [`Computable`] from another
    // Computable this method
    // returns a Real of Irrational class with that value.
    fn make_computable<F>(self, convert: F) -> Self
    where
        F: FnOnce(Computable) -> Computable,
    {
        let computable = convert(self.fold());

        Self {
            rational: Rational::one(),
            class: Irrational,
            computable,
            signal: None,
        }
    }

    /// The inverse of this Real, or a [`Problem`] if that's impossible,
    /// in particular Problem::DivideByZero if this real is zero.
    ///
    /// Example
    /// ```
    /// use realistic::{Rational,Real};
    /// let five = Real::new(Rational::new(5));
    /// let a_fifth = Real::new(Rational::fraction(1, 5).unwrap());
    /// assert_eq!(five.inverse(), Ok(a_fifth));
    /// ```
    pub fn inverse(self) -> Result<Self, Problem> {
        if self.definitely_zero() {
            return Err(Problem::DivideByZero);
        }
        match &self.class {
            One => {
                return Ok(Self {
                    rational: self.rational.inverse()?,
                    class: One,
                    computable: Computable::one(),
                    signal: None,
                });
            }
            Sqrt(sqrt) => {
                if let Some(sqrt) = sqrt.to_big_integer() {
                    let rational = (self.rational * Rational::from_bigint(sqrt)).inverse()?;
                    return Ok(Self {
                        rational,
                        class: self.class,
                        computable: self.computable,
                        signal: None,
                    });
                }
            }
            Exp(exp) => {
                let exp = Neg::neg(exp.clone());
                return Ok(Self {
                    rational: self.rational.inverse()?,
                    class: Exp(exp.clone()),
                    computable: Computable::e(exp),
                    signal: None,
                });
            }
            _ => (),
        }
        Ok(Self {
            rational: self.rational.inverse()?,
            class: Irrational,
            computable: Computable::inverse(self.computable),
            signal: None,
        })
    }

    /// The square root of this Real, or a [`Problem`] if that's impossible,
    /// in particular Problem::SqrtNegative if this Real is negative.
    pub fn sqrt(self) -> Result<Real, Problem> {
        if self.best_sign() == Sign::Minus {
            return Err(Problem::SqrtNegative);
        }
        if self.definitely_zero() {
            return Ok(Self::zero());
        }
        match &self.class {
            One => {
                if self.rational.extract_square_will_succeed() {
                    let (square, rest) = self.rational.extract_square_reduced();
                    if rest == *rationals::ONE {
                        return Ok(Self {
                            rational: square,
                            class: One,
                            computable: Computable::one(),
                            signal: None,
                        });
                    } else {
                        return Ok(Self {
                            rational: square,
                            class: Sqrt(rest.clone()),
                            computable: Computable::sqrt_rational(rest),
                            signal: None,
                        });
                    }
                }
            }
            Pi => {
                if self.rational.extract_square_will_succeed() {
                    let (square, rest) = self.rational.clone().extract_square_reduced();
                    if rest == *rationals::ONE {
                        return Ok(Self {
                            rational: square,
                            class: Irrational,
                            computable: Computable::sqrt(self.computable),
                            signal: None,
                        });
                    }
                }
            }
            Exp(exp) => {
                if self.rational.extract_square_will_succeed() {
                    let (square, rest) = self.rational.clone().extract_square_reduced();
                    if rest == *rationals::ONE {
                        let exp = exp.clone() / Rational::new(2);
                        return Ok(Self {
                            rational: square,
                            class: Exp(exp.clone()),
                            computable: Computable::e(exp),
                            signal: None,
                        });
                    }
                }
            }
            _ => (),
        }

        Ok(self.make_computable(Computable::sqrt))
    }

    /// Apply the exponential function to this Real parameter.
    pub fn exp(self) -> Result<Real, Problem> {
        if self.definitely_zero() {
            return Ok(Self::new(Rational::one()));
        }
        match &self.class {
            One => {
                return Ok(Self {
                    rational: Rational::one(),
                    class: Exp(self.rational.clone()),
                    computable: Computable::e(self.rational),
                    signal: None,
                });
            }
            Ln(ln) => {
                if let Some(int) = self.rational.to_big_integer() {
                    return Ok(Self {
                        rational: ln.clone().powi(int)?,
                        class: One,
                        computable: Computable::one(),
                        signal: None,
                    });
                }
            }
            _ => (),
        }

        Ok(self.make_computable(Computable::exp))
    }

    /// The base 10 logarithm of this Real or Problem::NotANumber if this Real is negative.
    pub fn log10(self) -> Result<Real, Problem> {
        use num::bigint::ToBigInt;

        self.ln()?
            / Self {
                rational: Rational::one(),
                class: LN10.clone(),
                computable: Computable::ln(Computable::integer(ToBigInt::to_bigint(&10).unwrap())),
                signal: None,
            }
    }

    // Find Some(m) integral log with respect to this base or else None
    // n should be positive (not zero) and base should be >= 2
    fn integer_log(n: &BigUint, base: u32) -> Option<u64> {
        use num::Integer;
        use num::bigint::ToBigUint;
        // TODO weed out some large failure cases early and return None

        // Calculate base^2 base^4 base^8 base^16 and so on until it is bigger than next
        let mut result: Option<u64> = None;
        let mut powers: Vec<BigUint> = Vec::new();
        let mut next = ToBigUint::to_biguint(&base).unwrap();
        powers.push(next.clone());

        let mut reduced = n.clone();
        let mut i = 1;
        loop {
            // TODO Looping, may need to handle cancellation
            next = next.pow(2);
            if next.bits() > reduced.bits() {
                break;
            }

            let (div, rem) = reduced.div_rem(&next);
            if rem != BigUint::ZERO {
                return None;
            }
            powers.push(next.clone());
            result = Some(result.unwrap_or(0) + (1 << i));
            reduced = div;
            i += 1;
        }

        while let Some(power) = powers.pop() {
            if reduced == *unsigned::ONE {
                break;
            }
            i -= 1;
            if power.bits() > reduced.bits() {
                continue;
            }
            let (div, rem) = reduced.div_rem(&power);
            if rem != BigUint::ZERO {
                return None;
            }
            result = Some(result.unwrap_or(0) + (1 << i));
            reduced = div;
        }

        if reduced == *unsigned::ONE {
            result
        } else {
            None
        }
    }

    // For input y = ln(r) with r positive gives
    // Some(k ln(s)) where there is a small integer m such that r = s^k.
    // or None
    fn ln_small(r: &Rational) -> Option<Real> {
        let n = r.to_big_integer()?;
        let n = n.magnitude();

        for base in [2, 3, 5, 6, 7, 10] {
            if let Some(n) = Self::integer_log(n, base) {
                let r = Rational::new(base as i64);
                let new = Computable::rational(r.clone());
                return Some(Self {
                    rational: Rational::new(n as i64),
                    class: Ln(r),
                    computable: Computable::ln(new),
                    signal: None,
                });
            }
        }

        None
    }

    // Ensure the resulting Real uses r > 1 for Ln(r)
    // this is convenient elsewhere and makes commonality more frequent
    // e.g. use Ln(2) rather than Ln(0.5)
    // Must be called with r > 0
    fn ln_rational(r: Rational) -> Result<Real, Problem> {
        use std::cmp::Ordering::*;

        match r.partial_cmp(rationals::ONE.deref()) {
            Some(Less) => {
                let inv = r.inverse()?;
                if let Some(answer) = Self::ln_small(&inv) {
                    return Ok(-answer);
                }
                let new = Computable::rational(inv.clone());
                Ok(Self {
                    rational: Rational::new(-1),
                    class: Ln(inv),
                    computable: Computable::ln(new),
                    signal: None,
                })
            }
            Some(Equal) => Ok(Self::zero()),
            Some(Greater) => {
                if let Some(answer) = Self::ln_small(&r) {
                    return Ok(answer);
                }
                let new = Computable::rational(r.clone());
                Ok(Self {
                    rational: Rational::one(),
                    class: Ln(r),
                    computable: Computable::ln(new),
                    signal: None,
                })
            }
            _ => unreachable!(),
        }
    }

    /// The natural logarithm of this Real or Problem::NotANumber if this Real is negative.
    pub fn ln(self) -> Result<Real, Problem> {
        if self.best_sign() != Sign::Plus {
            return Err(Problem::NotANumber);
        }
        match &self.class {
            One => return Self::ln_rational(self.rational),
            Exp(exp) => {
                if self.rational == *rationals::ONE {
                    return Ok(Self {
                        rational: exp.clone(),
                        class: One,
                        computable: Computable::one(),
                        signal: None,
                    });
                }
            }
            _ => (),
        }

        Ok(self.make_computable(Computable::ln))
    }

    /// The error function, erf(x) = (2/√π) ∫₀ˣ e^(−t²) dt. Defined for every real x;
    /// erf(0) = 0 exactly, otherwise Irrational.
    pub fn erf(self) -> Real {
        if self.definitely_zero() {
            return Self::zero();
        }
        self.make_computable(Computable::erf)
    }

    /// Standard normal CDF, Φ(x) = ½(1 + erf(x/√2)). Φ(0) = ½ exactly; otherwise
    /// Irrational. The argument is capped at ±[`PNORM_MAX_ABS`]; beyond that Φ is
    /// within ~10⁻²³ of 0 or 1 and the erf series is impractically slow, so we
    /// reject rather than hang ([`Problem::Exhausted`]).
    pub fn pnorm(self) -> Result<Real, Problem> {
        if self.definitely_zero() {
            return Ok(Self::new(rationals::HALF.clone()));
        }
        let xd: f64 = self.clone().into();
        if !xd.is_finite() || xd.abs() > PNORM_MAX_ABS {
            return Err(Problem::Exhausted);
        }
        Ok(self.make_computable(Computable::pnorm))
    }

    /// Standard normal density, φ(x) = e^(−x²/2) / √(2π). Always Irrational. Like
    /// [`pnorm`] the argument is capped at ±[`PNORM_MAX_ABS`]; beyond that φ is below
    /// ~10⁻²³ and evaluating e^(−x²/2) grows impractically expensive, so we reject
    /// ([`Problem::Exhausted`]) rather than risk hanging.
    ///
    /// [`pnorm`]: Real::pnorm
    pub fn dnorm(self) -> Result<Real, Problem> {
        let xd: f64 = self.clone().into();
        if !xd.is_finite() || xd.abs() > PNORM_MAX_ABS {
            return Err(Problem::Exhausted);
        }
        Ok(self.make_computable(Computable::dnorm))
    }

    /// Standard normal quantile, Φ⁻¹(p) for p in (0, 1) — the inverse of [`pnorm`].
    ///
    /// We invert the strictly-increasing CDF with a dedicated Newton iteration using
    /// the analytic derivative φ (see [`Computable::normal_quantile`]), seeded from a
    /// double-precision estimate. Returns [`Problem::NotANumber`] for p ∉ (0, 1) and
    /// [`Problem::Exhausted`] for p so close to 0 or 1 that Φ⁻¹(p) would exceed the
    /// ±[`PNORM_MAX_ABS`] cap.
    ///
    /// [`pnorm`]: Real::pnorm
    pub fn qnorm(self) -> Result<Real, Problem> {
        // Domain: p must lie in (0, 1).
        if self.best_sign() != Sign::Plus {
            return Err(Problem::NotANumber); // p <= 0
        }
        if self == *rationals::HALF {
            return Ok(Self::zero()); // Φ⁻¹(½) = 0 exactly
        }
        if self.is_rational() && self.rational >= *rationals::ONE {
            return Err(Problem::NotANumber); // p >= 1
        }

        let folded = self.clone().fold();
        // p >= 1 for the non-rational case, decided by exact CR comparison.
        if folded.compare_absolute(&Computable::one(), DEFAULT_COMPARE_TOLERANCE) != Ordering::Less
        {
            return Err(Problem::NotANumber);
        }
        // p must lie strictly inside (Φ(−cap), Φ(cap)); outside that, Φ⁻¹(p) would
        // exceed ±cap. Compare against the cap probabilities directly -- a double
        // seed is unreliable in the extreme tails (doubleValue underflows to 0 or
        // rounds to 1).
        if folded.compare_absolute(&pnorm_cap_lo(), DEFAULT_COMPARE_TOLERANCE) != Ordering::Greater {
            return Err(Problem::Exhausted); // too close to 0
        }
        if folded.compare_absolute(&pnorm_cap_hi(), DEFAULT_COMPARE_TOLERANCE) != Ordering::Less {
            return Err(Problem::Exhausted); // too close to 1
        }

        // Seed: work in the small tail (≤ ½, well resolved as a double). doubleValue
        // rounds p to exactly 1.0 once p is within ~1e-16 of 1, so compute 1 − p
        // EXACTLY as a Real first, then convert. Solve Φ(y) = p_small for y ≤ 0, then
        // Φ⁻¹(p) = ±y by the symmetry Φ⁻¹(p) = −Φ⁻¹(1 − p).
        let p_f64: f64 = self.clone().into();
        let upper_half = p_f64 > 0.5;
        let p_small = if upper_half {
            let one_minus = Self::new(Rational::one()) - self.clone();
            let v: f64 = one_minus.into();
            v.max(1e-300)
        } else {
            p_f64.max(1e-300)
        };
        let y = qnorm_approx(p_small); // ≈ negative
        let seed = (if upper_half { -y } else { y }).clamp(-PNORM_MAX_ABS, PNORM_MAX_ABS);
        // Acklam is good to ~1.2e-9 < 2⁻²⁹; claim only 2⁻²⁴ so the seed honours
        // approx's <1 ulp contract at the Newton recursion's base case.
        let seed_prec: Precision = -24;
        let seed_int = BigInt::from((seed * f64::from(1u32 << 24)).round() as i64);

        let q = Computable::normal_quantile(folded, seed_int, seed_prec);
        Ok(Self {
            rational: Rational::one(),
            class: Irrational,
            computable: q,
            signal: None,
        })
    }

    /// The sine of this Real.
    pub fn sin(self) -> Real {
        if self.definitely_zero() {
            return Self::zero();
        }
        match &self.class {
            One => {
                let new = Computable::rational(self.rational.clone());
                return Self {
                    rational: Rational::one(),
                    class: Irrational,
                    computable: Computable::sin(new),
                    signal: None,
                };
            }
            Pi => {
                if self.rational.is_integer() {
                    return Self::zero();
                }
                let mut r: Option<Real> = None;
                let d = self.rational.denominator();
                if d == unsigned::TWO.deref() {
                    r = Some(Self::new(Rational::one()));
                }
                if d == unsigned::THREE.deref() {
                    r = Some(Self {
                        rational: Rational::fraction(1, 2).unwrap(),
                        class: Sqrt(Rational::new(3)),
                        computable: Computable::sqrt_rational(Rational::new(3)),
                        signal: None,
                    });
                }
                if d == unsigned::FOUR.deref() {
                    r = Some(Self {
                        rational: Rational::fraction(1, 2).unwrap(),
                        class: Sqrt(Rational::new(2)),
                        computable: Computable::sqrt_rational(Rational::new(2)),
                        signal: None,
                    });
                }
                if d == unsigned::SIX.deref() {
                    r = Some(Self::new(Rational::fraction(1, 2).unwrap()));
                }
                if let Some(real) = r {
                    let whole = self.rational.shifted_big_integer(0);
                    if whole.bit(0) {
                        return real.neg();
                    } else {
                        return real;
                    }
                } else {
                    let (neg, r) = curve(self.rational);
                    let new =
                        Computable::multiply(Computable::pi(), Computable::rational(r.clone()));
                    if neg {
                        return Self {
                            rational: Rational::new(-1),
                            class: SinPi(r),
                            computable: Computable::sin(new),
                            signal: None,
                        };
                    } else {
                        return Self {
                            rational: Rational::one(),
                            class: SinPi(r),
                            computable: Computable::sin(new),
                            signal: None,
                        };
                    }
                }
            }
            _ => (),
        }

        self.make_computable(Computable::sin)
    }

    /// The cosine of this Real.
    pub fn cos(self) -> Real {
        if self.definitely_zero() {
            return Self::new(Rational::one());
        }
        match &self.class {
            One => {
                let new = Computable::rational(self.rational.clone());
                return Self {
                    rational: Rational::one(),
                    class: Irrational,
                    computable: Computable::cos(new),
                    signal: None,
                };
            }
            Pi => {
                let off = Self {
                    rational: self.rational + Rational::fraction(1, 2).unwrap(),
                    class: Pi,
                    computable: self.computable,
                    signal: None,
                };
                return off.sin();
            }
            _ => (),
        }

        self.make_computable(Computable::cos)
    }

    /// The tangent of this Real.
    pub fn tan(self) -> Result<Real, Problem> {
        if self.definitely_zero() {
            return Ok(Self::zero());
        }

        match &self.class {
            One => {
                let new = Computable::rational(self.rational.clone());
                return Ok(Self {
                    rational: Rational::one(),
                    class: Irrational,
                    computable: Computable::tan(new),
                    signal: None,
                });
            }
            Pi => {
                if self.rational.is_integer() {
                    return Ok(Self::zero());
                }
                let (neg, n) = tan_curve(self.rational);
                let mut r: Option<Real> = None;
                let d = n.denominator();
                if d == unsigned::TWO.deref() {
                    return Err(Problem::NotANumber);
                }
                if d == unsigned::THREE.deref() {
                    r = Some(Self {
                        rational: Rational::one(),
                        class: Sqrt(Rational::new(3)),
                        computable: Computable::sqrt_rational(Rational::new(3)),
                        signal: None,
                    });
                }
                if d == unsigned::FOUR.deref() {
                    r = Some(Self::new(Rational::one()));
                }
                if d == unsigned::SIX.deref() {
                    r = Some(Self {
                        rational: Rational::fraction(1, 3).unwrap(),
                        class: Sqrt(Rational::new(3)),
                        computable: Computable::sqrt_rational(Rational::new(3)),
                        signal: None,
                    });
                }
                if let Some(real) = r {
                    if neg {
                        return Ok(real.neg());
                    } else {
                        return Ok(real);
                    }
                } else {
                    let new =
                        Computable::multiply(Computable::pi(), Computable::rational(n.clone()));
                    if neg {
                        return Ok(Self {
                            rational: Rational::new(-1),
                            class: TanPi(n),
                            computable: Computable::tan(new),
                            signal: None,
                        });
                    } else {
                        return Ok(Self {
                            rational: Rational::one(),
                            class: TanPi(n),
                            computable: Computable::tan(new),
                            signal: None,
                        });
                    }
                }
            }
            _ => (),
        }
        let s = self.clone().sin();
        let c = self.cos();
        s / c
    }

    fn recursive_powi(base: &Real, exp: &BigUint) -> Self {
        if exp == unsigned::ONE.deref() {
            return base.clone();
        }
        let mut result = Self::new(Rational::one());
        for b in (0..(exp.bits())).rev() {
            result = result.clone() * result;
            if exp.bit(b) {
                result = result * base.clone();
            }
        }
        result
    }

    fn compute_exp_ln_powi(value: Computable, exp: BigInt) -> Option<Computable> {
        match value.sign() {
            Sign::NoSign => None,
            Sign::Plus => Some(value.ln().multiply(Computable::integer(exp)).exp()),
            Sign::Minus => {
                // Take the power of the positive version and negate it afterwards.
                let value = value.negate();
                let odd = exp.bit(0);
                let exp = Computable::integer(exp);
                if odd {
                    Some(value.ln().multiply(exp).exp().negate())
                } else {
                    Some(value.ln().multiply(exp).exp())
                }
            }
        }
    }

    fn exp_ln_powi(self, exp: BigInt) -> Result<Self, Problem> {
        match self.best_sign() {
            Sign::NoSign => {
                if exp.sign() == Sign::Minus {
                    Ok(Self::recursive_powi(&self, exp.magnitude()).neg())
                } else {
                    Ok(Self::recursive_powi(&self, exp.magnitude()))
                }
            }
            Sign::Plus => {
                let value = self.fold();
                let exp = Computable::integer(exp);

                Ok(Self {
                    rational: Rational::one(),
                    class: Irrational,
                    computable: value.ln().multiply(exp).exp(),
                    signal: None,
                })
            }
            Sign::Minus => {
                let odd = exp.bit(0);
                let value = self.fold();
                let exp = Computable::integer(exp);
                if odd {
                    Ok(Self {
                        rational: Rational::one(),
                        class: Irrational,
                        computable: value.ln().multiply(exp).exp().negate(),
                        signal: None,
                    })
                } else {
                    Ok(Self {
                        rational: Rational::one(),
                        class: Irrational,
                        computable: value.ln().multiply(exp).exp(),
                        signal: None,
                    })
                }
            }
        }
    }

    /// Raise this Real to some integer exponent.
    pub fn powi(self, exp: BigInt) -> Result<Self, Problem> {
        if exp == *signed::ONE {
            return Ok(self);
        }
        if exp.sign() == Sign::NoSign {
            if self.definitely_zero() {
                return Err(Problem::NotANumber);
            } else {
                return Ok(Self::new(Rational::one()));
            }
        }
        if exp.sign() == Sign::Minus && self.definitely_zero() {
            return Err(Problem::NotANumber);
        }
        if let Ok(rational) = self.rational.clone().powi(exp.clone()) {
            match &self.class {
                One => {
                    return Ok(Self {
                        rational,
                        class: One,
                        computable: self.computable,
                        signal: None,
                    });
                }
                Sqrt(sqrt) => 'quick: {
                    let odd = exp.bit(0);
                    let Ok(rf2) = sqrt.clone().powi(exp.clone() >> 1) else {
                        break 'quick;
                    };
                    let product = rational * rf2;
                    if odd {
                        let n = Self {
                            rational: product,
                            class: Sqrt(sqrt.clone()),
                            computable: self.computable,
                            signal: None,
                        };
                        return Ok(n);
                    } else {
                        return Ok(Self::new(product));
                    }
                }
                _ => {
                    if let Some(computable) =
                        Self::compute_exp_ln_powi(self.computable.clone(), exp.clone())
                    {
                        return Ok(Self {
                            rational,
                            class: Irrational,
                            computable,
                            signal: None,
                        });
                    }
                }
            }
        }
        self.exp_ln_powi(exp)
    }

    /// Fractional (Non-integer) rational exponent.
    fn pow_fraction(self, exponent: Rational) -> Result<Self, Problem> {
        if exponent.denominator() == unsigned::TWO.deref() {
            let n = exponent.shifted_big_integer(1);
            self.powi(n)?.sqrt()
        } else {
            self.pow_arb(Real::new(exponent))
        }
    }

    /// Arbitrary, possibly irrational exponent.
    /// NB: Assumed not to be integer
    fn pow_arb(self, exponent: Self) -> Result<Self, Problem> {
        match self.best_sign() {
            Sign::NoSign => {
                if exponent.best_sign() == Sign::Plus {
                    Ok(Real::zero())
                } else {
                    Err(Problem::NotAnInteger)
                }
            }
            Sign::Minus => Err(Problem::NotAnInteger),
            Sign::Plus => {
                let value = self.fold();
                let exp = exponent.fold();

                Ok(Self {
                    rational: Rational::one(),
                    class: Irrational,
                    computable: value.ln().multiply(exp).exp(),
                    signal: None,
                })
            }
        }
    }

    /// Raise this Real to some Real exponent.
    pub fn pow(self, exponent: Self) -> Result<Self, Problem> {
        if let Exp(ref n) = self.class {
            if n == rationals::ONE.deref() {
                if self.rational == *rationals::ONE {
                    return exponent.exp();
                } else {
                    let left = Real::new(self.rational).pow(exponent.clone())?;
                    return Ok(left * exponent.exp()?);
                }
            }
        }
        /* could handle self == 10 =>  10 ^ log10(exponent) specially */
        if exponent.class == One {
            let r = exponent.rational;
            match r.to_big_integer() {
                Some(n) => {
                    return self.powi(n);
                }
                None => {
                    return self.pow_fraction(r);
                }
            }
        }
        if exponent.definitely_zero() {
            return self.powi(BigInt::ZERO);
        }
        self.pow_arb(exponent)
    }

    /// Is this Real an integer ?
    pub fn is_integer(&self) -> bool {
        self.class == One && self.rational.is_integer()
    }

    /// Is this Real known to be rational ?
    pub fn is_rational(&self) -> bool {
        self.class == One
    }

    /// Should we display this Real as a fraction ?
    pub fn prefer_fraction(&self) -> bool {
        self.class == One && self.rational.prefer_fraction()
    }
}

use core::fmt;

impl Real {
    /// Format this Real as a decimal rather than rational.
    /// Scientific notation will be used if the value is very large or small.
    pub fn decimal(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let folded = self.clone().fold();
        match folded.iter_msd_stop(-20) {
            Some(-19..60) => fmt::Display::fmt(&folded, f),
            _ => fmt::LowerExp::fmt(&folded, f),
        }
    }
}

impl fmt::UpperExp for Real {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let folded = self.clone().fold();
        folded.fmt(f)
    }
}

impl fmt::LowerExp for Real {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let folded = self.clone().fold();
        folded.fmt(f)
    }
}

impl fmt::Display for Real {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if f.alternate() {
            self.decimal(f)
        } else {
            self.rational.fmt(f)?;
            match &self.class {
                One => Ok(()),
                Pi => f.write_str(" Pi"),
                Exp(n) => write!(f, " x e**({})", &n),
                Ln(n) => write!(f, " x ln({})", &n),
                Log10(n) => write!(f, " x log10({})", &n),
                Sqrt(n) => write!(f, " √({})", &n),
                SinPi(n) => write!(f, " x sin({} x Pi)", &n),
                TanPi(n) => write!(f, " x tan({} x Pi)", &n),
                _ => write!(f, " x {:?}", self.class),
            }
        }
    }
}

impl std::str::FromStr for Real {
    type Err = Problem;

    fn from_str(s: &str) -> Result<Self, Problem> {
        let rational: Rational = s.parse()?;
        Ok(Self {
            rational,
            class: One,
            computable: Computable::one(),
            signal: None,
        })
    }
}

use std::ops::*;

impl Real {
    fn simple_log_sum(
        a: Rational,
        b: Rational,
        c: Rational,
        d: Rational,
    ) -> Result<Rational, Problem> {
        let Some(a) = a.to_big_integer() else {
            return Err(Problem::NotAnInteger);
        };
        let Some(c) = c.to_big_integer() else {
            return Err(Problem::NotAnInteger);
        };
        /* TODO: Should not attempt to simplify once a, b, c, d are too big */
        let left = b.powi(a)?;
        let right = d.powi(c)?;
        Ok(left * right)
    }
}

impl Add for Real {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        if self.class == other.class {
            let rational = self.rational + other.rational;
            if rational.sign() == Sign::NoSign {
                return Self::zero();
            } else {
                return Self { rational, ..self };
            }
        }
        if self.definitely_zero() {
            return other;
        }
        if other.definitely_zero() {
            return self;
        }
        if self.class.is_ln() && other.class.is_ln() {
            let Ln(b) = self.class.clone() else {
                unreachable!()
            };
            let Ln(d) = other.class.clone() else {
                unreachable!()
            };
            if let Ok(r) = Self::simple_log_sum(self.rational.clone(), b, other.rational.clone(), d)
            {
                if let Ok(simple) = Self::ln_rational(r) {
                    return simple;
                }
            }
        }
        let left = self.fold();
        let right = other.fold();
        let computable = Computable::add(left, right);
        Self {
            rational: Rational::one(),
            class: Irrational,
            computable,
            signal: None,
        }
    }
}

impl Neg for Real {
    type Output = Self;

    fn neg(self) -> Self {
        Self {
            rational: -self.rational,
            ..self
        }
    }
}

impl Sub for Real {
    type Output = Self;

    fn sub(self, other: Self) -> Self {
        self + -other
    }
}

impl Real {
    fn multiply_sqrts(x: Rational, y: Rational) -> Self {
        if x == y {
            Self {
                rational: x,
                class: One,
                computable: Computable::one(),
                signal: None,
            }
        } else {
            let product = x * y;
            if product == *rationals::ZERO {
                return Self {
                    rational: product,
                    class: One,
                    computable: Computable::one(),
                    signal: None,
                };
            }
            let (a, b) = product.extract_square_reduced();
            if b == *rationals::ONE {
                return Self {
                    rational: a,
                    class: One,
                    computable: Computable::one(),
                    signal: None,
                };
            }
            Self {
                rational: a,
                class: Sqrt(b.clone()),
                computable: Computable::sqrt_rational(b),
                signal: None,
            }
        }
    }
}

impl Mul for Real {
    type Output = Self;

    fn mul(self, other: Self) -> Self {
        if self.definitely_zero() || other.definitely_zero() {
            return Self::zero();
        }
        if self.class == One {
            let rational = self.rational * other.rational;
            return Self { rational, ..other };
        }
        if other.class == One {
            let rational = self.rational * other.rational;
            return Self { rational, ..self };
        }
        match (self.class, other.class) {
            (Sqrt(r), Sqrt(s)) => {
                let square = Self::multiply_sqrts(r, s);
                Self {
                    rational: square.rational * self.rational * other.rational,
                    ..square
                }
            }
            (Exp(r), Exp(s)) => {
                let (class, computable) = Class::make_exp(r + s);
                let rational = self.rational * other.rational;
                Self {
                    rational,
                    class,
                    computable,
                    signal: None,
                }
            }
            (Pi, Pi) => {
                let rational = self.rational * other.rational;
                Self {
                    rational,
                    class: Irrational,
                    computable: Computable::square(Computable::pi()),
                    signal: None,
                }
            }
            _ => {
                let rational = self.rational * other.rational;
                Self {
                    rational,
                    class: Irrational,
                    computable: Computable::multiply(self.computable, other.computable),
                    signal: None,
                }
            }
        }
    }
}

impl Div for Real {
    type Output = Result<Self, Problem>;

    fn div(self, other: Self) -> Result<Self, Problem> {
        use num::bigint::ToBigInt;

        if other.definitely_zero() {
            return Err(Problem::DivideByZero);
        }
        if self.definitely_zero() {
            return Ok(Self::zero());
        }
        if self.class == other.class {
            let rational = self.rational / other.rational;
            return Ok(Self::new(rational));
        }
        if other.class == One {
            let rational = self.rational / other.rational;
            return Ok(Self { rational, ..self });
        }

        // Simplify ln(x) / ln(10) to just log10(x)
        if other.class.is_ln() && self.class.is_ln() {
            if let Ln(s) = other.class.clone() {
                if s == *rationals::TEN {
                    let Ln(r) = self.class else {
                        unreachable!();
                    };
                    let rational = self.rational / other.rational;
                    let computable = self.computable.multiply(
                        Computable::integer(ToBigInt::to_bigint(&10).unwrap())
                            .ln()
                            .inverse(),
                    );
                    return Ok(Self {
                        rational,
                        class: Log10(r),
                        computable,
                        ..self
                    });
                }
            } else {
                unreachable!();
            }
        }

        let inverted = other.inverse()?;
        Ok(self * inverted)
    }
}

// Best efforts only, definitely not adequate for Eq
// Requirements: PartialEq should be transitive and symmetric
// however it needn't be complete or reflexive.
impl PartialEq for Real {
    fn eq(&self, other: &Self) -> bool {
        self.rational == other.rational && self.class == other.class
    }
}

// For a rational this definitely works
impl PartialEq<Rational> for Real {
    fn eq(&self, other: &Rational) -> bool {
        self.class == Class::One && self.rational == *other
    }
}

// Symmetry
impl PartialEq<Real> for Rational {
    fn eq(&self, other: &Real) -> bool {
        other.class == Class::One && *self == other.rational
    }
}

