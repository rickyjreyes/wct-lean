import Mathlib
import WCTLean.Models.ComplexCurvature

/-!
# Uniform global positivity of the corrected complex WCT denominator

For epsilon > 0 and alpha >= 0, the denominator
  D(s) = s + epsilon^2 * exp(-2*alpha*s)
has a strictly positive **global** floor on the full half-line s >= 0:
  D(s) >= epsilon^2 * exp(-2*alpha*epsilon^2).

This is stronger than pointwise nonvanishing; the bound does NOT require
a uniform L-infinity bound on the field. It is a necessary analytic
ingredient for nonlinear quotient estimates but does not alone give
H^2 mapping regularity, local Lipschitz control or a PDE solution.
-/

namespace WCTLean

/-- A uniform state-independent lower bound for the corrected denominator. -/
noncomputable def complexRegulatorFloor (epsilon alpha : ℝ) : ℝ :=
  epsilon ^ 2 * Real.exp (-2 * alpha * epsilon ^ 2)

/-- The global denominator floor is strictly positive when epsilon > 0. -/
theorem complexRegulatorFloor_pos (epsilon alpha : ℝ)
    (heps : 0 < epsilon) :
    0 < complexRegulatorFloor epsilon alpha := by
  unfold complexRegulatorFloor
  exact mul_pos (sq_pos_of_pos heps) (Real.exp_pos _)

/-- The exact corrected regulator has a field-independent positive lower
bound on every nonnegative squared-modulus state, if alpha >= 0. -/
theorem radialComplexDenominator_ge_floor
    (s epsilon alpha : ℝ) (hs : 0 ≤ s)
    (heps : 0 < epsilon) (ha : 0 ≤ alpha) :
    complexRegulatorFloor epsilon alpha ≤
      s + epsilon ^ 2 * Real.exp (-2 * alpha * s) := by
  have hepsSq : 0 ≤ epsilon ^ 2 := sq_nonneg epsilon
  by_cases hsmall : s ≤ epsilon ^ 2
  · have hproduct : 0 ≤ alpha * (epsilon ^ 2 - s) :=
      mul_nonneg ha (sub_nonneg.mpr hsmall)
    have harg : -2 * alpha * epsilon ^ 2 ≤ -2 * alpha * s := by
      nlinarith
    have hexp := (Real.exp_le_exp).mpr harg
    have hscale := mul_le_mul_of_nonneg_left hexp hepsSq
    unfold complexRegulatorFloor
    linarith
  · have hlarge : epsilon ^ 2 ≤ s := le_of_lt (lt_of_not_ge hsmall)
    have hproduct : 0 ≤ alpha * epsilon ^ 2 := mul_nonneg ha hepsSq
    have harg : -2 * alpha * epsilon ^ 2 ≤ 0 := by nlinarith
    have hexp : Real.exp (-2 * alpha * epsilon ^ 2) ≤ 1 := by
      have h := (Real.exp_le_exp).mpr harg
      simpa only [Real.exp_zero] using h
    have hscale := mul_le_mul_of_nonneg_left hexp hepsSq
    have hterm : 0 ≤ epsilon ^ 2 * Real.exp (-2 * alpha * s) := by positivity
    unfold complexRegulatorFloor
    linarith

/-- The corrected complex M2/E17 denominator is uniformly separated from
zero over every complex field value, without an amplitude cutoff. -/
theorem complexRegularizerDenominator_ge_uniformFloor
    (psi : ℂ) (epsilon alpha : ℝ)
    (heps : 0 < epsilon) (ha : 0 ≤ alpha) :
    complexRegulatorFloor epsilon alpha ≤
      complexRegularizerDenominator psi epsilon alpha := by
  exact radialComplexDenominator_ge_floor
    (Complex.normSq psi) epsilon alpha
    (Complex.normSq_nonneg psi) heps ha

/-- An arbitrary field on any spatial domain inherits the **same**
pointwise positive floor. Regularity of the field is not assumed or
proved by this statement. -/
theorem complexField_denominator_uniformFloor
    {X : Type*} (psi : X → ℂ) (epsilon alpha : ℝ)
    (heps : 0 < epsilon) (ha : 0 ≤ alpha) :
    ∀ x : X, complexRegulatorFloor epsilon alpha ≤
      complexRegularizerDenominator (psi x) epsilon alpha := by
  intro x
  exact complexRegularizerDenominator_ge_uniformFloor (psi x)
    epsilon alpha heps ha

end WCTLean
