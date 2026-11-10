import Mathlib

/-!
# Genuine first- and second-order integration by parts for S004

These are actual real interval-integral theorems proved by Mathlib's
fundamental theorem of calculus, NOT axiomatized Green identities.
They provide the exact sign and boundary cancellation required for
the temporal acceleration, velocity and one-dimensional spatial
gradient/Laplacian terms in the original higher-order S004 variation.

The zero-endpoint versions apply to compactly supported-in-time test
variations; the periodic versions apply to smooth coefficients and
variations whose function values and first derivatives match across
the spatial period cell. Multidimensional Sobolev/Fubini assembly
remains a separate analytic obligation.
-/

open MeasureTheory Set
open scoped Interval

namespace WCTLean.S004IntervalGreen

/-- Actual first-order Green identity for a scalar variation vanishing
at both endpoints; all derivative and integrability hypotheses are
explicit, and the boundary term is actually eliminated. -/
theorem integral_mul_first_deriv_eq_neg
    (a b : ℝ) (u u1 v v1 : ℝ → ℝ)
    (hu : ∀ x ∈ [[a,b]], HasDerivAt u (u1 x) x)
    (hv : ∀ x ∈ [[a,b]], HasDerivAt v (v1 x) x)
    (huInt : IntervalIntegrable u1 volume a b)
    (hvInt : IntervalIntegrable v1 volume a b)
    (hva : v a = 0) (hvb : v b = 0) :
    (∫ x in a..b, u x * v1 x) =
      -(∫ x in a..b, u1 x * v x) := by
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := u) (v := v) (u' := u1) (v' := v1)
    hu hv huInt hvInt
  simpa [hva, hvb] using h

/-- The first-order Green identity on an actual periodic interval cell,
where both endpoint traces agree. This does not postulate a skew
adjoint operator; it is proved directly from the interval integral. -/
theorem integral_mul_first_deriv_periodic
    (a b : ℝ) (u u1 v v1 : ℝ → ℝ)
    (hu : ∀ x ∈ [[a,b]], HasDerivAt u (u1 x) x)
    (hv : ∀ x ∈ [[a,b]], HasDerivAt v (v1 x) x)
    (huInt : IntervalIntegrable u1 volume a b)
    (hvInt : IntervalIntegrable v1 volume a b)
    (huPer : u b = u a) (hvPer : v b = v a) :
    (∫ x in a..b, u x * v1 x) =
      -(∫ x in a..b, u1 x * v x) := by
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := u) (v := v) (u' := u1) (v' := v1)
    hu hv huInt hvInt
  simpa [huPer, hvPer] using h

/-- **Genuine second-order time integration by parts** for a
compactly supported smooth test variation with both value and first
derivative vanishing at the time endpoints:
∫ u * (∂tt v) = ∫ (∂tt u) * v.
The two cancellations follow from two applications of the actual
fundamental theorem of calculus. -/
theorem integral_mul_second_deriv_eq
    (a b : ℝ) (u u1 u2 v v1 v2 : ℝ → ℝ)
    (hu : ∀ x ∈ [[a,b]], HasDerivAt u (u1 x) x)
    (hu1 : ∀ x ∈ [[a,b]], HasDerivAt u1 (u2 x) x)
    (hv : ∀ x ∈ [[a,b]], HasDerivAt v (v1 x) x)
    (hv1 : ∀ x ∈ [[a,b]], HasDerivAt v1 (v2 x) x)
    (hu1Int : IntervalIntegrable u1 volume a b)
    (hu2Int : IntervalIntegrable u2 volume a b)
    (hv1Int : IntervalIntegrable v1 volume a b)
    (hv2Int : IntervalIntegrable v2 volume a b)
    (hva : v a = 0) (hvb : v b = 0)
    (hv1a : v1 a = 0) (hv1b : v1 b = 0) :
    (∫ x in a..b, u x * v2 x) =
      (∫ x in a..b, u2 x * v x) := by
  have hfirst := integral_mul_first_deriv_eq_neg
    a b u u1 v1 v2 hu hv1 hu1Int hv2Int hv1a hv1b
  have hsecond := integral_mul_first_deriv_eq_neg
    a b u1 u2 v v1 hu1 hv hu2Int hv1Int hva hvb
  calc
    (∫ x in a..b, u x * v2 x) =
        -(∫ x in a..b, u1 x * v1 x) := hfirst
    _ = (∫ x in a..b, u2 x * v x) := by rw [hsecond]; ring

/-- **Genuine second-order spatial integration by parts on a periodic
cell.** Both coefficients and test variations have matching 0th-
and 1st-order traces. This is a concrete self-adjointness identity
for the second spatial derivative on periodic smooth data. -/
theorem integral_mul_second_deriv_periodic
    (a b : ℝ) (u u1 u2 v v1 v2 : ℝ → ℝ)
    (hu : ∀ x ∈ [[a,b]], HasDerivAt u (u1 x) x)
    (hu1 : ∀ x ∈ [[a,b]], HasDerivAt u1 (u2 x) x)
    (hv : ∀ x ∈ [[a,b]], HasDerivAt v (v1 x) x)
    (hv1 : ∀ x ∈ [[a,b]], HasDerivAt v1 (v2 x) x)
    (hu1Int : IntervalIntegrable u1 volume a b)
    (hu2Int : IntervalIntegrable u2 volume a b)
    (hv1Int : IntervalIntegrable v1 volume a b)
    (hv2Int : IntervalIntegrable v2 volume a b)
    (huPer : u b = u a) (hu1Per : u1 b = u1 a)
    (hvPer : v b = v a) (hv1Per : v1 b = v1 a) :
    (∫ x in a..b, u x * v2 x) =
      (∫ x in a..b, u2 x * v x) := by
  have hfirst := integral_mul_first_deriv_periodic
    a b u u1 v1 v2 hu hv1 hu1Int hv2Int huPer hv1Per
  have hsecond := integral_mul_first_deriv_periodic
    a b u1 u2 v v1 hu1 hv hu2Int hv1Int hu1Per hvPer
  calc
    (∫ x in a..b, u x * v2 x) =
        -(∫ x in a..b, u1 x * v1 x) := hfirst
    _ = (∫ x in a..b, u2 x * v x) := by rw [hsecond]; ring

end WCTLean.S004IntervalGreen
