use crate::Computable;
use crate::Rational;
use crate::computable::{Precision, Signal, scale, shift, should_stop, signed};
use num::ToPrimitive;
use num::bigint::{Sign, ToBigInt};
use num::{BigInt, BigUint, Signed};
use num::{One, Zero};
use std::ops::Deref;

#[derive(Clone, Debug)]
pub(super) enum Approximation {
    Int(BigInt),
    Inverse(Computable),
    Negate(Computable),
    Add(Computable, Computable),
    Multiply(Computable, Computable),
    Square(Computable),
    Ratio(Rational),
    Offset(Computable, i32),
    PrescaledExp(Computable),
    Sqrt(Computable),
    PrescaledLn(Computable),
    IntegralAtan(BigInt),
    PrescaledCos(Computable),
    ErfSeries(Computable),
    NormalQuantile {
        p: Computable,
        seed: BigInt,
        seed_prec: Precision,
    },
}

impl Approximation {
    pub fn approximate(&self, signal: &Option<Signal>, p: Precision) -> BigInt {
        use Approximation::*;

        match self {
            Int(i) => scale(i.clone(), -p),
            Inverse(c) => inverse(signal, c, p),
            Negate(c) => -c.approx_signal(signal, p),
            Add(c1, c2) => add(signal, c1, c2, p),
            Multiply(c1, c2) => multiply(signal, c1, c2, p),
            Square(c) => square(signal, c, p),
            Ratio(r) => ratio(r, p),
            Offset(c, n) => offset(signal, c, *n, p),
            PrescaledExp(c) => exp(signal, c, p),
            Sqrt(c) => sqrt(signal, c, p),
            PrescaledLn(c) => ln(signal, c, p),
            IntegralAtan(i) => atan(signal, i, p),
            PrescaledCos(c) => cos(signal, c, p),
            ErfSeries(c) => erf_series(signal, c, p),
            NormalQuantile {
                p: prob,
                seed,
                seed_prec,
            } => normal_quantile(signal, prob, seed, *seed_prec, p),
        }
    }
}

fn inverse(signal: &Option<Signal>, c: &Computable, p: Precision) -> BigInt {
    let msd = c.iter_msd();
    let inv_msd = 1 - msd;
    let digits_needed = inv_msd - p + 3;
    let prec_needed = msd - digits_needed;
    let log_scale_factor = -p - prec_needed;

    if log_scale_factor < 0 {
        return Zero::zero();
    }

    let dividend = signed::ONE.deref() << log_scale_factor;
    let scaled_divisor = c.approx_signal(signal, prec_needed);
    let abs_scaled_divisor = scaled_divisor.abs();
    let adj_dividend = dividend + (&abs_scaled_divisor >> 1);
    let result: BigInt = adj_dividend / abs_scaled_divisor;

    if scaled_divisor.sign() == Sign::Minus {
        -result
    } else {
        result
    }
}

fn add(signal: &Option<Signal>, c1: &Computable, c2: &Computable, p: Precision) -> BigInt {
    scale(
        c1.approx_signal(signal, p - 2) + c2.approx_signal(signal, p - 2),
        -2,
    )
}

fn multiply(signal: &Option<Signal>, c1: &Computable, c2: &Computable, p: Precision) -> BigInt {
    let half_prec = (p >> 1) - 1;

    match c1.msd(half_prec) {
        None => match c2.msd(half_prec) {
            None => Zero::zero(),
            Some(msd_op2) => {
                let prec1 = p - msd_op2 - 3;
                let appr1 = c1.approx_signal(signal, prec1);

                if appr1.sign() == Sign::NoSign {
                    return Zero::zero();
                }

                let msd_op1 = c1.known_msd();
                let prec2 = p - msd_op1 - 3;
                let appr2 = c2.approx_signal(signal, prec2);

                let scale_digits = prec2 + prec1 - p;
                scale(appr2 * appr1, scale_digits)
            }
        },
        Some(msd_op1) => {
            let prec2 = p - msd_op1 - 3;
            let appr2 = c2.approx_signal(signal, prec2);

            if appr2.sign() == Sign::NoSign {
                return Zero::zero();
            }

            let msd_op2 = c2.known_msd();
            let prec1 = p - msd_op2 - 3;
            let appr1 = c1.approx_signal(signal, prec1);

            let scale_digits = prec1 + prec2 - p;
            scale(appr1 * appr2, scale_digits)
        }
    }
}

fn square(signal: &Option<Signal>, c: &Computable, p: Precision) -> BigInt {
    let half_prec = (p >> 1) - 1;
    let prec2 = match c.msd(half_prec) {
        None => {
            return Zero::zero();
        }
        Some(msd) => p - msd - 3,
    };

    let appr2 = c.approx_signal(signal, prec2);

    if appr2.sign() == Sign::NoSign {
        return Zero::zero();
    }

    let msd_op2 = c.known_msd();
    let prec1 = p - msd_op2 - 3;
    let appr1 = c.approx_signal(signal, prec1);

    let scale_digits = prec1 + prec2 - p;
    scale(appr1 * appr2, scale_digits)
}

fn ratio(r: &Rational, p: Precision) -> BigInt {
    if p >= 0 {
        scale(r.shifted_big_integer(0), -p)
    } else {
        r.shifted_big_integer(-p)
    }
}

fn offset(signal: &Option<Signal>, c: &Computable, n: i32, p: Precision) -> BigInt {
    c.approx_signal(signal, p - n)
}

fn bound_log2(n: i32) -> i32 {
    let abs_n = n.abs();
    let ln2 = 2.0_f64.ln();
    let n_plus_1: f64 = (abs_n + 1).into();
    let ans: f64 = (n_plus_1.ln() / ln2).ceil();
    ans as i32
}

/* Only intended for Computable values < 0.5, others will be pre-scaled
 * in Computable::exp */
fn exp(signal: &Option<Signal>, c: &Computable, p: Precision) -> BigInt {
    if p >= 1 {
        return Zero::zero();
    }

    let iterations_needed = -p / 2 + 2;
    //  Claim: each intermediate term is accurate
    //  to 2*2^calc_precision.
    //  Total rounding error in series computation is
    //  2*iterations_needed*2^calc_precision,
    //  exclusive of error in op.
    let calc_precision = p - bound_log2(2 * iterations_needed) - 4; // for error in op, truncation.
    let op_prec = p - 3;

    let op_appr = c.approx_signal(signal, op_prec);

    // Error in argument results in error of < 3/8 ulp.
    // Sum of term eval. rounding error is < 1/16 ulp.
    // Series truncation error < 1/16 ulp.
    // Final rounding error is <= 1/2 ulp.
    // Thus final error is < 1 ulp.
    let scaled_1 = signed::ONE.deref() << -calc_precision;

    let max_trunc_error = signed::ONE.deref() << (p - 4 - calc_precision);
    let mut current_term = scaled_1.clone();
    let mut sum = scaled_1;
    let mut n = BigInt::zero();

    while current_term.abs() > max_trunc_error {
        if should_stop(signal) {
            break;
        }
        n += signed::ONE.deref();
        current_term = scale(current_term * &op_appr, op_prec) / &n;
        sum += &current_term;
    }

    scale(sum, calc_precision - p)
}

fn sqrt(signal: &Option<Signal>, c: &Computable, p: Precision) -> BigInt {
    let fp_prec: i32 = 50;
    let fp_op_prec: i32 = 60;

    let max_prec_needed = 2 * p - 1;
    let msd = c.msd(max_prec_needed).unwrap_or(Precision::MIN);

    if msd <= max_prec_needed {
        return Zero::zero();
    }

    if should_stop(signal) {
        return signed::ONE.deref().clone();
    }

    let result_msd = msd / 2;
    let result_digits = result_msd - p;

    if result_digits > fp_prec {
        // Compute less precise approximation and use a Newton iter.
        let appr_digits = result_digits / 2 + 6;
        // This should be conservative.  Is fewer enough?
        let appr_prec = result_msd - appr_digits;

        let last_appr = sqrt(signal, c, appr_prec);
        let prod_prec = 2 * appr_prec;

        let op_appr = c.approx_signal(signal, prod_prec);

        // Slightly fewer might be enough;
        // Compute (last_appr * last_appr + op_appr)/(last_appr/2)
        // while adjusting the scaling to make everything work

        let prod_prec_scaled_numerator = (&last_appr * &last_appr) + op_appr;
        let scaled_numerator = scale(prod_prec_scaled_numerator, appr_prec - p);

        let shifted_result = scaled_numerator / last_appr;

        (shifted_result + signed::ONE.deref()) / signed::TWO.deref()
    } else {
        // Use an approximation from the Num crate
        // Make sure all precisions are even
        let op_prec = (msd - fp_op_prec) & !1;
        let working_prec = op_prec - fp_op_prec;

        let scaled_bi_appr = c.approx_signal(signal, op_prec) << fp_op_prec;

        let scaled_sqrt = scaled_bi_appr.sqrt();

        let shift_count = working_prec / 2 - p;
        shift(scaled_sqrt, shift_count)
    }
}

// Compute cosine of |c| < 1
// uses a Taylor series expansion.
fn cos(signal: &Option<Signal>, c: &Computable, p: Precision) -> BigInt {
    if p >= 1 {
        return signed::ONE.deref().clone();
    }
    let iterations_needed = -p / 2 + 4;

    if should_stop(signal) {
        return signed::ONE.deref().clone();
    }

    //  Claim: each intermediate term is accurate
    //  to 2*2^calc_precision.
    //  Total rounding error in series computation is
    //  2*iterations_needed*2^calc_precision,
    //  exclusive of error in op.
    let calc_precision = p - bound_log2(2 * iterations_needed) - 4; // for error in op, truncation.
    let op_prec = p - 2;
    let op_appr = c.approx_signal(signal, op_prec);

    // Error in argument results in error of < 1/4 ulp.
    // Cumulative arithmetic rounding error is < 1/16 ulp.
    // Series truncation error < 1/16 ulp.
    // Final rounding error is <= 1/2 ulp.
    // Thus final error is < 1 ulp.

    let max_trunc_error = signed::ONE.deref() << (p - 4 - calc_precision);
    let mut n = 0;
    let mut current_term = signed::ONE.deref() << (-calc_precision);
    let mut current_sum = current_term.clone();

    while current_term.abs() > max_trunc_error {
        if should_stop(signal) {
            break;
        }
        n += 2;

        /* current_term = - current_term * op * op / n * (n - 1)   */
        current_term = scale(current_term * &op_appr, op_prec);
        current_term = scale(current_term * &op_appr, op_prec);
        let divisor = ToBigInt::to_bigint(&-n).unwrap() * ToBigInt::to_bigint(&(n - 1)).unwrap();
        current_term /= divisor;

        current_sum += &current_term;
    }
    scale(current_sum, calc_precision - p)
}

// Compute an approximation of ln(1+x) to precision p.
// This assumes |x| < 1/2.
// It uses a Taylor series expansion.
// Unfortunately there appears to be no way to take
// advantage of old information.
// Note: this is known to be a bad algorithm for
// floating point.  Unfortunately, other alternatives
// appear to require precomputed tabular information.
fn ln(signal: &Option<Signal>, c: &Computable, p: Precision) -> BigInt {
    if p >= 0 {
        return Zero::zero();
    }

    let iterations_needed = -p;
    let calc_precision = p - bound_log2(2 * iterations_needed) - 4;
    let op_prec = p - 3;
    let op_appr = c.approx_signal(signal, op_prec);

    let mut x_nth = scale(op_appr.clone(), op_prec - calc_precision);
    let mut current_term = x_nth.clone();
    let mut sum = current_term.clone();

    let mut n = 1;
    let mut sign = 1;

    let max_trunc_error = signed::ONE.deref() << (p - 4 - calc_precision);

    while current_term.abs() > max_trunc_error {
        if should_stop(signal) {
            break;
        }
        n += 1;
        sign = -sign;
        x_nth = scale(&x_nth * &op_appr, op_prec);

        let divisor: BigInt = (n * sign).into();
        current_term = &x_nth / divisor;
        sum += &current_term;
    }

    scale(sum, calc_precision - p)
}

// Approximate the Arctangent of 1/n where n is some small integer > base
// what is "base" in this context?
fn atan(signal: &Option<Signal>, i: &BigInt, p: Precision) -> BigInt {
    if p >= 1 {
        return Zero::zero();
    }

    let iterations_needed: i32 = -p / 2 + 2; // conservative estimate > 0.
    // from Java implementation description:

    // Claim: each intermediate term is accurate
    // to 2*base^calc_precision.
    // Total rounding error in series computation is
    // 2*iterations_needed*base^calc_precision,
    // exclusive of error in op.

    let calc_precision = p - bound_log2(2 * iterations_needed) - 2;
    // Error in argument results in error of < 3/8 ulp.
    // Cumulative arithmetic rounding error is < 1/4 ulp.
    // Series truncation error < 1/4 ulp.
    // Final rounding error is <= 1/2 ulp.
    // Thus final error is < 1 ulp.

    let max_trunc_error: BigUint = BigUint::one() << (p - 2 - calc_precision);

    let scaled_1 = signed::ONE.deref() << (-calc_precision);
    let big_op_squared: BigInt = i * i;
    let inverse: BigInt = scaled_1 / i;

    let mut current_power = inverse.clone();
    let mut current_term = inverse.clone();
    let mut sum = inverse;

    let mut sign = 1;
    let mut n = 1;

    while *current_term.magnitude() > max_trunc_error {
        if should_stop(signal) {
            break;
        }
        n += 2;
        current_power /= &big_op_squared;
        sign = -sign;
        let signed_n: BigInt = (n * sign).into();
        current_term = &current_power / signed_n;
        sum += &current_term;
    }

    scale(sum, calc_precision - p)
}

// Convert a (non-negative) BigInt to a Precision, saturating on overflow. Only
// fed by erf_series's term/magnitude bounds, which are tiny for capped inputs.
fn to_prec(n: &BigInt) -> Precision {
    n.to_i32().unwrap_or(Precision::MAX)
}

// S(x) = Σ_{n≥0} 2ⁿ·x^(2n+1)/(2n+1)!!, the cancellation-free core of erf(x) (see
// Computable::erf). Every term shares x's sign and the ratio a_{n+1}/a_n =
// 2x²/(2n+3) is strictly decreasing, so once a term shrinks past its predecessor
// the entire remainder is bounded by a geometric series. S(x) itself grows like
// e^(x²); the e^(−x²) factor applied by erf cancels it.
fn erf_series(signal: &Option<Signal>, op: &Computable, p: Precision) -> BigInt {
    let rough_x = op.approx_signal(signal, -10); // ≈ x·2¹⁰
    let x_sq_approx = (&rough_x * &rough_x) >> 20; // ≈ x²  (≥ 0)

    // Conservative upper bound on the number of terms: ~x² (to reach the peak)
    // plus the requested precision. Only feeds the guard-bit count logarithmically.
    let n_estimate = {
        let e = &x_sq_approx + BigInt::from(-p) + BigInt::from(10);
        if e < BigInt::one() { BigInt::one() } else { e }
    };
    // Guard bits must cover BOTH the term count (rounding accumulates over the
    // recurrence) AND the magnitude of the largest partial sum. The all-positive
    // series peaks at S = (√π/2)·e^(x²)·erf(x) < e^(x²), so msd(S) ≤ x²·log₂(e).
    // 3/2 > log₂(e) gives a safe upper bound.
    let magnitude_bits = to_prec(&((&x_sq_approx * BigInt::from(3)) / BigInt::from(2))) + 2;
    let guard_bits = (n_estimate.magnitude().bits() as Precision) + magnitude_bits + 4;
    let calc_precision = p - guard_bits;
    let op_prec = calc_precision - 8; // a bit extra for x itself
    let op_appr = op.approx_signal(signal, op_prec);
    let max_trunc_error = signed::ONE.deref() << (p - 4 - calc_precision);

    let mut n: i64 = 0;
    let mut current_term = scale(op_appr.clone(), op_prec - calc_precision); // a₀ = x
    let mut current_sum = current_term.clone();
    loop {
        if should_stop(signal) {
            break;
        }
        let prev = current_term;
        // a_{n+1} = a_n · x · x · 2/(2n+3)
        let mut t = scale(&prev * &op_appr, op_prec);
        t = scale(t * &op_appr, op_prec);
        t = (t * signed::TWO.deref()) / BigInt::from(2 * n + 3);
        n += 1;
        if t.is_zero() {
            break; // x == 0 or underflow
        }
        let prev_abs = prev.abs();
        let cur_abs = t.abs();
        if cur_abs < prev_abs {
            // Past the peak (ratio < 1): the tail from t onward, t·Σρᵏ, is
            // ≤ cur_abs·prev_abs/(prev_abs − cur_abs). Stop before adding t.
            let denom = &prev_abs - &cur_abs;
            if &cur_abs * &prev_abs < &max_trunc_error * &denom {
                break;
            }
        }
        current_sum += &t;
        current_term = t;
    }
    scale(current_sum, calc_precision - p)
}

// |Φ⁻¹| < cap ≤ 10 ⇒ the result's msd is ≤ 5 (with slop). Like Sqrt's result_msd,
// this only schedules the half-precision recursion; an over-estimate merely adds a
// Newton level, never wrong digits.
const RESULT_MSD_BOUND: Precision = 5;

// Φ⁻¹(p), the standard-normal quantile, by Newton's method with the *analytic*
// derivative:  x_{n+1} = x_n − (Φ(x_n) − p) / φ(x_n).  This avoids inverting Φ with
// a generic monotone inverter: Newton with the exact derivative is self-correcting
// and never estimates the derivative numerically, so it stays robust where Φ is
// nearly flat (the deep tails). Structure mirrors Sqrt: recurse at ~half precision
// (bottoming out at the coarse double `seed`) then do one Newton step, which
// quadratically doubles the correct digits.
fn normal_quantile(
    signal: &Option<Signal>,
    p: &Computable,
    seed: &BigInt,
    seed_prec: Precision,
    prec: Precision,
) -> BigInt {
    // Base case: the coarse double seed, scaled to the requested precision.
    if prec >= seed_prec || should_stop(signal) {
        return scale(seed.clone(), seed_prec - prec);
    }
    // x_n at ~half precision; the recursion bottoms out at the seed once apprPrec is
    // coarse enough (apprPrec is always coarser than prec here).
    let appr_prec = (RESULT_MSD_BOUND + prec) / 2 - 6;
    let xn_int = normal_quantile(signal, p, seed, seed_prec, appr_prec);
    let xn = Computable::integer(xn_int).shift_left(appr_prec);
    let fx = xn.clone().pnorm(); // Φ(x_n)
    let phi_xn = xn.clone().dnorm(); // φ(x_n)
    let x_next = xn.subtract(fx.subtract(p.clone()).divide(phi_xn));
    // Evaluate two bits beyond and round, to absorb the Newton truncation and stay
    // within the <1 ulp approx contract.
    (x_next.approx_signal(signal, prec - 2) + signed::TWO.deref()) >> 2
}
