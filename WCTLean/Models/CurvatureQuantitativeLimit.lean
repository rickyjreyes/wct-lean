import Mathlib
import WCTLean.Models.ComplexCurvature

/-!
# Quantitative vanishing-regulator control away from field nodes (issue #22)

For the *unchanged* corrected M2/E17 denominator
  D_epsilon(z) = |z|² + epsilon² exp(-2 alpha |z|²),
the real scalar inverse has an O(epsilon²) uniform error on every
set |z|² >= delta > 0 whenever alpha >= 0.

This is a genuine bound, not merely an identity or a pointwise tendsto.
It concerns the denominator reciprocal used in the exact complex
quotient; multiplying by the field conjugate and supplied Laplacian
requires separately certified bounds. No claim is made at field nodes,
or about energy, weak PDE solutions, or nonlinear flow convergence.
-/

namespace WCTLean

/-- Exact rational control with an explicit nonnodal lower bound.
This also applies to non-exponential positive regularizers. -/
theorem positive_reciprocal_regularization_bound
    (c a delta : ℝ) (hdelta : 0 < delta) (hdc : delta ≤ c)
    (ha : 0 ≤ a) :
    |(1 : ℝ) / (c + a) - (1 : ℝ) / c| ≤ a / delta ^ 2 := by
  have hc : 0 < c := lt_of_lt_of_le hdelta hdc
  have hd : 0 < c + a := by linarith
  have hdeltaSq : 0 < delta ^ 2 := sq_pos_of_pos hdelta
  have hsq1 : delta ^ 2 ≤ c ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hdc)
      (add_nonneg (le_of_lt hc) (le_of_lt hdelta))]
  have hsq2 : c ^ 2 ≤ c * (c + a) := by
    nlinarith [mul_nonneg (le_of_lt hc) ha]
  have hsq : delta ^ 2 ≤ c * (c + a) := le_trans hsq1 hsq2
  have hid : (1 : ℝ) / (c + a) - (1 : ℝ) / c =
      -(a / (c * (c + a))) := by
    field_simp [ne_of_gt hc, ne_of_gt hd]
    ring
  calc
    |(1 : ℝ) / (c + a) - (1 : ℝ) / c|
        = a / (c * (c + a)) := by
          rw [hid, abs_neg, abs_div, abs_of_nonneg ha,
            abs_of_pos (mul_pos hc hd)]
    _ ≤ a / delta ^ 2 := by
          exact (div_le_div_iff₀ (mul_pos hc hd) hdeltaSq).2
            (mul_le_mul_of_nonneg_left hsq ha)

/-- Nonnodal quantitative inverse-denominator error for the *actual*
modulus-squared corrected WCT regularizer. No alpha sign is needed here. -/
theorem complex_regularizer_inverse_error
    (psi : ℂ) (epsilon alpha delta : ℝ)
    (hdelta : 0 < delta) (hpsi : delta ≤ Complex.normSq psi) :
    |(1 : ℝ) / complexRegularizerDenominator psi epsilon alpha -
      (1 : ℝ) / Complex.normSq psi| ≤
      (epsilon ^ 2 * Real.exp (-2 * alpha * Complex.normSq psi)) /
        delta ^ 2 := by
  have ha : 0 ≤ epsilon ^ 2 * Real.exp (-2 * alpha * Complex.normSq psi) :=
    mul_nonneg (sq_nonneg _) (le_of_lt (Real.exp_pos _))
  simpa only [complexRegularizerDenominator] using
    positive_reciprocal_regularization_bound
      (Complex.normSq psi)
      (epsilon ^ 2 * Real.exp (-2 * alpha * Complex.normSq psi))
      delta hdelta hpsi ha

/-- For nonnegative alpha, the preceding local error is controlled
by epsilon²/delta² uniformly over all states with |psi|² >= delta.
This bound vanishes quadratically in the regulator without an upper
amplitude cutoff. Nodal states are deliberately excluded. -/
theorem complex_regularizer_inverse_uniform_quadratic
    (psi : ℂ) (epsilon alpha delta : ℝ)
    (hdelta : 0 < delta) (hpsi : delta ≤ Complex.normSq psi)
    (halpha : 0 ≤ alpha) :
    |(1 : ℝ) / complexRegularizerDenominator psi epsilon alpha -
      (1 : ℝ) / Complex.normSq psi| ≤ epsilon ^ 2 / delta ^ 2 := by
  have hnorm : 0 ≤ Complex.normSq psi := Complex.normSq_nonneg psi
  have harg : -2 * alpha * Complex.normSq psi ≤ 0 := by
    nlinarith [mul_nonneg halpha hnorm]
  have hexp : Real.exp (-2 * alpha * Complex.normSq psi) ≤ 1 := by
    have h := (Real.exp_le_exp).mpr harg
    simpa only [Real.exp_zero] using h
  have hprod :
      epsilon ^ 2 * Real.exp (-2 * alpha * Complex.normSq psi) ≤ epsilon ^ 2 := by
    calc
      epsilon ^ 2 * Real.exp (-2 * alpha * Complex.normSq psi)
          ≤ epsilon ^ 2 * 1 := mul_le_mul_of_nonneg_left hexp (sq_nonneg _)
      _ = epsilon ^ 2 := by ring
  have hdeltaSq : 0 < delta ^ 2 := sq_pos_of_pos hdelta
  have hfrac :
      epsilon ^ 2 * Real.exp (-2 * alpha * Complex.normSq psi) /
          delta ^ 2 ≤ epsilon ^ 2 / delta ^ 2 :=
    (div_le_div_iff₀ hdeltaSq hdeltaSq).2
      (mul_le_mul_of_nonneg_right hprod hdeltaSq.le)
  exact le_trans
    (complex_regularizer_inverse_error psi epsilon alpha delta hdelta hpsi) hfrac

/-! ## Full complex curvature operator, pointwise estimate -/

/-- The exact corrected complex curvature operator may be factored through
the real reciprocal denominator without adding an assumption or changing
its definition. This identity includes the original supplied Laplacian. -/
theorem thetaComplex_as_real_reciprocal (lapPsi psi : ℂ)
    (epsilon alpha : ℝ) :
    thetaComplex lapPsi psi epsilon alpha =
      (-lapPsi * star psi) *
        ((1 / complexRegularizerDenominator psi epsilon alpha : ℝ) : ℂ) := by
  unfold thetaComplex complexRegularizedReciprocal
  push_cast
  ring

/-- A quantitative pointwise estimate for the FULL complex curvature
quotient with a fixed supplied Laplacian. The norm is the complex modulus;
the result is not a PDE convergence theorem. -/
theorem thetaComplex_nonnodal_error_bound
    (lapPsi psi : ℂ) (epsilon alpha delta : ℝ)
    (hdelta : 0 < delta) (hpsi : delta ≤ Complex.normSq psi)
    (halpha : 0 ≤ alpha) :
    ‖thetaComplex lapPsi psi epsilon alpha -
      thetaComplex lapPsi psi 0 alpha‖ ≤
      ‖lapPsi‖ * ‖psi‖ * (epsilon ^ 2 / delta ^ 2) := by
  have hzero :
      complexRegularizerDenominator psi 0 alpha = Complex.normSq psi := by
    simp [complexRegularizerDenominator]
  have hform :
      thetaComplex lapPsi psi epsilon alpha -
        thetaComplex lapPsi psi 0 alpha =
      (-lapPsi * star psi) *
        (((1 / complexRegularizerDenominator psi epsilon alpha : ℝ) -
          (1 / Complex.normSq psi : ℝ)) : ℂ) := by
    rw [thetaComplex_as_real_reciprocal,
      thetaComplex_as_real_reciprocal, hzero]
    rw [← mul_sub]
    congr 1
    push_cast
  rw [hform, norm_mul, norm_mul, norm_neg, norm_star, ← Complex.ofReal_sub, Complex.norm_real]
  have herr := complex_regularizer_inverse_uniform_quadratic
    psi epsilon alpha delta hdelta hpsi halpha
  have hfac : 0 ≤ ‖lapPsi‖ * ‖psi‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  nlinarith [mul_le_mul_of_nonneg_left herr hfac]

/-- Uniform pointwise convergence of the full quotient on a nodal-free
field family with certified Laplacian and amplitude bounds. This is an
explicit quantitative estimate for every spatial point, independent
of the spatial domain type. -/
theorem thetaComplex_field_uniform_error
    {X : Type*} (lapPsi psi : X → ℂ)
    (epsilon alpha delta lapBound ampBound : ℝ)
    (hdelta : 0 < delta) (halpha : 0 ≤ alpha)
    (hlap : ∀ x, ‖lapPsi x‖ ≤ lapBound)
    (hamp : ∀ x, ‖psi x‖ ≤ ampBound)
    (hnodal : ∀ x, delta ≤ Complex.normSq (psi x)) :
    ∀ x,
      ‖thetaComplex (lapPsi x) (psi x) epsilon alpha -
        thetaComplex (lapPsi x) (psi x) 0 alpha‖ ≤
        lapBound * ampBound * (epsilon ^ 2 / delta ^ 2) := by
  intro x
  have hδ : 0 ≤ epsilon ^ 2 / delta ^ 2 :=
    div_nonneg (sq_nonneg _) (sq_nonneg _)
  have hL : 0 ≤ lapBound := le_trans (norm_nonneg _) (hlap x)
  have hA : 0 ≤ ampBound := le_trans (norm_nonneg _) (hamp x)
  calc
    ‖thetaComplex (lapPsi x) (psi x) epsilon alpha -
        thetaComplex (lapPsi x) (psi x) 0 alpha‖
      ≤ ‖lapPsi x‖ * ‖psi x‖ * (epsilon ^ 2 / delta ^ 2) :=
        thetaComplex_nonnodal_error_bound _ _ _ _ _ hdelta (hnodal x) halpha
    _ ≤ lapBound * ampBound * (epsilon ^ 2 / delta ^ 2) := by
        gcongr
        · exact hlap x
        · exact hamp x


end WCTLean
