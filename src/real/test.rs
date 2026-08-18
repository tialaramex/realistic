#[cfg(test)]
mod tests {
    use super::super::curve;
    use crate::{Problem, Rational, Real};

    #[test]
    fn zero() {
        assert_eq!(Real::zero(), Real::zero());
    }

    #[test]
    fn parse() {
        let counting: Real = "123456789".parse().unwrap();
        let answer = Real::new(Rational::new(123456789));
        assert_eq!(counting, answer);
    }

    #[test]
    fn parse_large() {
        let input: Real = "378089444731722233953867379643788100".parse().unwrap();
        let root = Rational::new(614889782588491410);
        let answer = Real::new(root.clone() * root);
        assert_eq!(input, answer);
    }

    #[test]
    fn parse_fraction() {
        let input: Real = "98760/123450".parse().unwrap();
        let answer = Real::new(Rational::fraction(9876, 12345).unwrap());
        assert_eq!(input, answer);
    }

    #[test]
    fn root_divide() {
        let twenty: Real = 20.into();
        let five: Real = 5.into();
        let a = twenty.sqrt().unwrap();
        let b = five.sqrt().unwrap().inverse().unwrap();
        let answer = a * b;
        let two: Real = 2.into();
        assert_eq!(answer, two);
    }

    #[test]
    fn rational() {
        let two: Real = 2.into();
        assert_ne!(two, Real::zero());
        let four: Real = 4.into();
        let answer = four - two;
        let two: Real = 2.into();
        assert_eq!(answer, two);
        let zero = answer - two;
        assert_eq!(zero, Real::zero());
        let six_half: Real = "13/2".parse().unwrap();
        let opposite = six_half.inverse().unwrap();
        let expected: Real = "2/13".parse().unwrap();
        assert_eq!(opposite, expected);
    }

    // https://devblogs.microsoft.com/oldnewthing/?p=93765
    // "Why does the Windows calculator generate tiny errors when calculating the square root of a
    // perfect square?" (fixed in 2018)
    #[test]
    fn perfect_square() {
        let four: Real = 4.into();
        let two: Real = 2.into();
        let calc = four.sqrt().unwrap() - two;
        assert_eq!(calc, Real::zero());
    }

    #[test]
    fn one_over_e() {
        let one: Real = 1.into();
        let e = Real::e();
        let e_inverse = Real::e().inverse().unwrap();
        let answer = e * e_inverse;
        assert_eq!(one, answer);
        let again = answer.sqrt().unwrap();
        assert_eq!(one, again);
    }

    #[test]
    fn unlike_sqrts() {
        let thirty: Real = 30.into();
        let ten: Real = 10.into();
        let answer = thirty.sqrt().unwrap() * ten.sqrt().unwrap();
        let ten: Real = 10.into();
        let three: Real = 3.into();
        let or = ten * three.sqrt().unwrap();
        assert_eq!(answer, or);
    }

    #[test]
    fn zero_pi() {
        let pi = Real::pi();
        let z1 = pi - Real::pi();
        let pi2 = Real::pi() + Real::pi();
        let z2 = pi2 * Real::zero();
        assert!(z1.definitely_zero());
        assert!(z2.definitely_zero());
        let two_pi = Real::pi() + Real::pi();
        let two: Real = 2.into();
        assert_eq!(two_pi, two * Real::pi());
        assert_ne!(two_pi, Rational::new(2));
    }

    #[test]
    fn ln_zero() {
        let zero = Real::zero();
        assert_eq!(zero.ln(), Err(Problem::NotANumber));
    }

    #[test]
    fn sqrt_exact() {
        let big: Real = 40_000.into();
        let small: Rational = Rational::new(200);
        let answer = big.sqrt().unwrap();
        assert_eq!(answer, small);
    }

    #[test]
    fn square_sqrt() {
        let two: Real = 2.into();
        let three: Real = 3.into();
        let small = three.sqrt().expect("Should be able to sqrt(n)");
        let a = small * two;
        let three: Real = 3.into();
        let small = three.sqrt().expect("Should be able to sqrt(n)");
        let three: Real = 3.into();
        let b = small * three;
        let answer = a * b;
        let eighteen: Rational = Rational::new(18);
        assert_eq!(answer, eighteen);
    }

    #[test]
    fn adding_one_works() {
        let pi = Real::pi();
        let one: Real = 1.into();
        let plus_one = pi + one;
        let float: f64 = plus_one.into();
        assert_eq!(float, 4.141592653589793);
    }

    #[test]
    fn sin_easy() {
        let pi = Real::pi();
        let zero = Real::zero();
        let two: Real = 2.into();
        let two_pi = pi.clone() * two;
        assert_eq!(zero.clone().sin(), zero);
        assert_eq!(pi.clone().sin(), zero);
        assert_eq!(two_pi.clone().sin(), zero);
    }

    #[test]
    fn cos_easy() {
        let pi = Real::pi();
        let zero = Real::zero();
        let one: Real = 1.into();
        let two: Real = 2.into();
        let two_pi = pi.clone() * two;
        let minus_one: Real = (-1).into();
        assert_eq!(zero.clone().cos(), one);
        assert_eq!(pi.clone().cos(), minus_one);
        assert_eq!(two_pi.clone().cos(), one);
    }

    #[test]
    fn powi() {
        let base: Real = 4.into();
        let five_over_two: Real = "5/2".parse().unwrap();
        let answer = base.pow(five_over_two).unwrap();
        let correct: Real = 32.into();
        assert_eq!(answer, correct);
    }

    #[test]
    fn sqrt_3045512() {
        use crate::real::Class::Sqrt;

        let n: Real = 3045512.into();
        let sqrt = n.sqrt().unwrap();
        let root = Rational::new(1234);
        assert_eq!(sqrt.rational, root);
        let two = Rational::new(2);
        assert_eq!(sqrt.class, Sqrt(two));
    }

    fn closest_f64(r: Real, f: f64) -> bool {
        let left = f64::from_bits(f.to_bits() - 1);
        let right = f64::from_bits(f.to_bits() + 1);
        let f: f64 = r.into();
        if right > left {
            left < f && right > f
        } else {
            left > f && right < f
        }
    }

    #[test]
    fn pow_pi() {
        let pi = Real::pi();
        let sq = pi.pow(Real::pi()).unwrap();
        assert!(closest_f64(sq.clone(), 36.46215960720791));
        let sqsq = sq.pow(Real::pi()).unwrap();
        assert!(closest_f64(sqsq, 80662.6659385546));
    }

    #[test]
    fn pow_fract() {
        let frac: Real = "-1.3".parse().unwrap();
        let five: Real = 5.into();
        let answer = frac.pow(five).unwrap();
        assert!(closest_f64(answer, -3.7129299999999996));
    }

    #[test]
    fn pow_of_sine() {
        let sin_10 = Real::new(Rational::new(10)).sin();
        let answer = (sin_10.clone()).pow(Real::new(Rational::new(2))).unwrap();
        assert!(closest_f64(
            answer,
            // Value from wolframalpha.com
            0.29595896909330400696886606953617752145
        ));
    }

    #[test]
    fn curves() {
        let eighty = Rational::fraction(80, 100).unwrap();
        let twenty = Rational::fraction(20, 100).unwrap();
        assert_eq!(curve(eighty), (false, twenty));
        let forty = Rational::fraction(40, 100).unwrap();
        let sixty = Rational::fraction(60, 100).unwrap();
        assert_eq!(curve(sixty), (false, forty));
        let otf = Rational::fraction(124, 100).unwrap();
        let tf = Rational::fraction(24, 100).unwrap();
        assert_eq!(curve(otf), (true, tf));
    }

    #[test]
    fn exp_pi() {
        let pi = Real::pi();
        assert_eq!(format!("{pi:.2e}"), "3.14e0");
        assert_eq!(format!("{pi:.4E}"), "3.1416E0");
        assert_eq!(format!("{pi:.8e}"), "3.14159265e0");
        assert_eq!(format!("{pi:.16E}"), "3.1415926535897932E0");
        assert_eq!(format!("{pi:.32e}"), "3.14159265358979323846264338327950e0");
        assert_eq!(format!("{pi:e}"), "3.1415926535897932384626433832795e0");
    }

    #[test]
    fn ln_division() {
        let fifth = Rational::fraction(2, 10).unwrap();
        let twenty_fifth = Rational::fraction(4, 100).unwrap();
        let ln_5th = Real::new(fifth).ln().unwrap();
        let ln_25th = Real::new(twenty_fifth).ln().unwrap();
        let answer = ln_25th / ln_5th;
        assert_eq!(answer.unwrap(), Rational::new(2));
    }

    #[test]
    fn integer_logs() {
        for (n, log) in [
            (1, 0),
            (10, 1),
            (10_000_000_000_000_000, 16),
            (100_000_000_000_000_000, 17),
            (1000_000_000_000_000_000, 18),
        ] {
            let n = Real::new(Rational::new(n));
            let answer = n.log10().unwrap();
            assert_eq!(answer, Rational::new(log));
        }
    }

    // pnorm (standard normal CDF) and qnorm (its quantile). Deep correctness is
    // pinned to an INDEPENDENT oracle (mpmath) at 1000 digits across the whole ±10
    // range in `against_mpmath_references`. Round trips (qnorm∘pnorm = id) and
    // symmetry are cheap self-consistency checks, but they can't catch a
    // wrong-but-consistent pair, which is why the oracle is the real test.
    mod normal {
        use crate::computable::Precision;
        use crate::real::normal_reference::CASES;
        use crate::{Computable, Problem, Rational, Real};
        use num::bigint::{BigInt, BigUint, Sign};
        use std::cmp::Ordering;
        use std::ops::Neg;

        // Assert v equals the high-precision decimal reference to within 2^bits, i.e.
        // far past f64 -- comparison is done on the exact constructive real, not the
        // lossy (±1 ulp) f64 conversion.
        fn close(v: Real, decimal: &str, bits: Precision) {
            let r: Rational = decimal.parse().unwrap();
            assert_eq!(
                v.fold().compare_absolute(&Computable::rational(r), bits),
                Ordering::Equal,
                "disagrees with {decimal}"
            );
        }

        fn ratio(n: i64, d: u64) -> Real {
            Real::new(Rational::fraction(n, d).unwrap())
        }

        // Build a Real from arbitrary-size numerator/denominator decimal strings.
        fn case_real(num: &str, den: &str) -> Real {
            let n: BigInt = num.parse().unwrap();
            let d: BigUint = den.parse().unwrap();
            Real::new(Rational::from_bigint_fraction(n, d).unwrap())
        }

        // The value truncated toward zero to `n` fractional digits, formatted like
        // mpmath's `int(floor(|x|·10ⁿ))` rendering used to freeze the references.
        fn trunc_str(real: &Real, n: usize) -> String {
            let neg = real.best_sign() == Sign::Minus;
            let c = real.clone().fold();
            // Enough bits to resolve n decimal digits (log₂10 ≈ 3.322) plus slack.
            let bits: Precision = -((n as Precision) * 3322 / 1000 + 64);
            let appr = c.approx(bits).magnitude().clone(); // ≈ |value|·2^-bits
            let ten_n: BigInt = num::pow::Pow::pow(BigInt::from(10), n as u32);
            let scaled = (BigInt::from(appr) * ten_n) >> ((-bits) as usize);
            let mut s = scaled.to_string();
            if s.len() <= n {
                s = format!("{}{}", "0".repeat(n - s.len() + 1), s);
            }
            let (int_part, frac_part) = s.split_at(s.len() - n);
            format!("{}{}.{}", if neg { "-" } else { "" }, int_part, frac_part)
        }

        // MARK: exact cases

        #[test]
        fn exact_cases() {
            // Φ(0) = ½ exactly.
            assert_eq!(Real::zero().pnorm().unwrap(), Rational::fraction(1, 2).unwrap());
            // Φ⁻¹(½) = 0 exactly.
            assert!(ratio(1, 2).qnorm().unwrap().definitely_zero());
            // erf(0) = 0 exactly.
            assert!(Real::zero().erf().definitely_zero());
        }

        // MARK: known values, pinned well past f64 (~38 digits)

        // erf and dnorm at the Real level, against references computed independently
        // (Python `decimal`) to ~44 digits. pnorm/qnorm get the full 1000-digit
        // treatment in `against_mpmath_references`; a couple are repeated here only to
        // confirm the Real wrappers and the entry points line up. Everything is checked
        // on the exact constructive real -- ~38 digits, more than twice what f64 holds.
        #[test]
        fn known_values() {
            close(ratio(1, 1).erf(), "0.8427007929497148693412206350826092592960", -120);
            close(
                Real::from(-1).erf(),
                "-0.8427007929497148693412206350826092592960",
                -120,
            );
            close(Real::zero().dnorm().unwrap(), "0.39894228040143267793994605993438186847", -120);
            close(ratio(1, 1).dnorm().unwrap(), "0.24197072451914334979783019293556065482", -120);
            close(ratio(2, 1).dnorm().unwrap(), "0.05399096651318805195056420041071358173", -120);
            close(ratio(1, 1).pnorm().unwrap(), "0.84134474606854294858523254563203792247", -120);
            close(
                Real::from(-3).pnorm().unwrap(),
                "0.00134989803163009452665181476759497737",
                -120,
            );
            close(ratio(975, 1000).qnorm().unwrap(), "1.95996398454005423552459443052055152795", -120);
        }

        // dnorm is the even density; φ(−x) = φ(x) and the ±cap rejects extreme args.
        #[test]
        fn density() {
            let two = ratio(2, 1);
            let rt = two.clone().dnorm().unwrap().fold();
            let neg = two.neg().dnorm().unwrap().fold();
            assert_eq!(
                rt.compare_absolute(&neg, -200),
                std::cmp::Ordering::Equal,
                "dnorm(-2) != dnorm(2)"
            );
            let big: Real = 600.into();
            assert_eq!(big.dnorm().unwrap_err(), Problem::Exhausted);
        }

        // MARK: deep self-consistency (no external reference needed)

        #[test]
        fn round_trip_and_symmetry() {
            // Spans the centre and the moderate tails (qnorm(pnorm(±5)) exercises the
            // analytic-derivative Newton inverter where Φ is already quite flat).
            let xs = [
                ratio(2, 1),
                (-1).into(),
                ratio(1, 2),
                ratio(3, 2),
                Real::from(4),
                Real::from(-5),
            ];
            for x in xs {
                // qnorm(pnorm(x)) == x to ~30 digits.
                let rt = x.clone().pnorm().unwrap().qnorm().unwrap();
                assert_eq!(
                    rt.fold().compare_absolute(&x.clone().fold(), -100),
                    std::cmp::Ordering::Equal,
                    "round trip failed for {x:?}"
                );
                // pnorm(x) + pnorm(-x) == 1 to ~30 digits.
                let sym = x.clone().pnorm().unwrap() + x.clone().neg().pnorm().unwrap();
                let one = Real::new(Rational::one());
                assert_eq!(
                    sym.fold().compare_absolute(&one.fold(), -100),
                    std::cmp::Ordering::Equal,
                    "symmetry failed for {x:?}"
                );
            }
        }

        // MARK: domain

        #[test]
        fn domain_errors() {
            assert_eq!(Real::zero().qnorm().unwrap_err(), Problem::NotANumber); // p = 0
            assert_eq!(ratio(1, 1).qnorm().unwrap_err(), Problem::NotANumber); // p = 1
            assert_eq!(ratio(2, 1).qnorm().unwrap_err(), Problem::NotANumber); // p > 1
            let minus_one: Real = (-1).into();
            assert_eq!(minus_one.qnorm().unwrap_err(), Problem::NotANumber); // p < 0
        }

        // Sanity cap: |x| past the (deliberately narrow, ±10) range is rejected
        // instead of running the erf series for ages.
        #[test]
        fn input_sanity_cap() {
            let neg_600: Real = (-600).into();
            assert_eq!(neg_600.pnorm().unwrap_err(), Problem::Exhausted);
            let eleven: Real = 11.into();
            assert_eq!(eleven.pnorm().unwrap_err(), Problem::Exhausted);
            let hundred: Real = 100.into();
            assert!(hundred.qnorm().is_err()); // p > 1 anyway, but also out of range
            let neg_nine: Real = (-9).into();
            assert!(neg_nine.pnorm().is_ok()); // inside the range still computes

            // Extreme probabilities whose quantile is beyond ±cap must REJECT, not
            // return the cap boundary (p ≈ 0 / p ≈ 1, where doubleValue underflows to
            // 0 / rounds to 1). We use clean rationals below/above the cap; Swift uses
            // e^±1e7 here, but evaluating that CR in this engine is intractable (~14M
            // bits) without UnifiedReal's symbolic short-circuit, and a rational past
            // the cap exercises exactly the same rejection branch.
            let tiny = case_real("1", "1000000000000000000000000000000"); // 1e-30 < cap_lo
            assert_eq!(tiny.clone().qnorm().unwrap_err(), Problem::Exhausted); // p ≈ 0
            let near_one = Real::new(Rational::one()) - tiny;
            assert_eq!(near_one.qnorm().unwrap_err(), Problem::Exhausted); // p ≈ 1

            // A feasible deep tail (|Φ⁻¹| < cap) still computes (≈ -9.26, not -10).
            let v: f64 = case_real("1", "100000000000000000000").qnorm().unwrap().into();
            assert!(v > -9.9 && v < -8.5, "qnorm(1e-20) = {v}");
        }

        // (qnorm correctness in the tails -- where a naive interpolating inverter
        // would return a bracket endpoint -- is covered to full precision by
        // `against_mpmath_references` at p = 1/10, 1/100, 1/10⁴ … and by the ±5 round
        // trips in `round_trip_and_symmetry`, so no separate loose-tolerance tail test
        // is kept.)

        // Regression: the EXTREME tails near the ±cap, where Φ is dead flat
        // (φ(9) ≈ 1e-18). These round trips are mathematically EXACT, so we assert
        // exact CR equality at high precision rather than a double snapshot.
        #[test]
        fn extreme_tails() {
            let prec = -140;
            // qnorm(pnorm(x)) = x, out to the cap, both signs.
            for (n, d) in [(99, 10), (90, 10), (70, 10), (-70, 10), (-90, 10), (-99, 10)] {
                let x = ratio(n, d);
                let rt = x.clone().pnorm().unwrap().qnorm().unwrap();
                assert_eq!(
                    rt.fold().compare_absolute(&x.clone().fold(), prec),
                    std::cmp::Ordering::Equal,
                    "qnorm(pnorm({n}/{d}))"
                );
            }
            // pnorm(qnorm(p)) = p for tiny p in BOTH tails (10⁻ᵏ and 1 − 10⁻ᵏ).
            for k in [8u32, 16, 20] {
                let den = num::pow::Pow::pow(BigInt::from(10), k).to_string();
                let lo = case_real("1", &den); // 10⁻ᵏ
                let rt = lo.clone().qnorm().unwrap().pnorm().unwrap();
                assert_eq!(
                    rt.fold().compare_absolute(&lo.clone().fold(), prec),
                    std::cmp::Ordering::Equal,
                    "pnorm(qnorm(1e-{k}))"
                );
                let hi = Real::new(Rational::one()) - lo; // 1 − 10⁻ᵏ
                let rt = hi.clone().qnorm().unwrap().pnorm().unwrap();
                assert_eq!(
                    rt.fold().compare_absolute(&hi.clone().fold(), prec),
                    std::cmp::Ordering::Equal,
                    "pnorm(qnorm(1-1e-{k}))"
                );
            }
        }

        // The real correctness test: 1000 digits against an INDEPENDENT oracle
        // (mpmath), not self-consistency. Spans the whole ±10 range including the
        // extremes (pnorm(±10), qnorm out to answers ≈ ±9.97). Compares the engine's
        // 1000-digit truncation digit-for-digit.
        #[test]
        fn against_mpmath_references() {
            for &(kind, num, den, expected) in CASES {
                let arg = case_real(num, den);
                let value = if kind == "pnorm" {
                    arg.pnorm().unwrap()
                } else {
                    arg.qnorm().unwrap()
                };
                let got = trunc_str(&value, 1000);
                assert_eq!(got, expected, "{kind}({num}/{den}) disagrees with mpmath");
            }
        }
    }
}
