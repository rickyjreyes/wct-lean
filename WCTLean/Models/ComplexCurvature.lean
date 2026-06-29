import Mathlib

namespace WCTLean

/-!
# Corrected complex curvature regularizer

This is the modulus-squared M2/E17 denominator from the corrected registry.
For `epsilon > 0` it is strictly positive for every complex field value,
including nodes where `psi = 0`.
-/

/-- The corrected real denominator
`|psi|^2 + epsilon^2 exp (-2 alpha |psi|^2)`. -/
noncomputable def complexRegularizerDenominator
    (psi : ℂ) (epsilon alpha : ℝ) : ℝ :=
  Complex.normSq psi + epsilon ^ 2 *
    Real.exp (-2 * alpha * Complex.normSq psi)

/-- The node-safe reciprocal replacing the historical scalar quotient. -/
noncomputable def complexRegularizedReciprocal
    (psi : ℂ) (epsilon alpha : ℝ) : ℂ :=
  star psi / (complexRegularizerDenominator psi epsilon alpha : ℂ)

/-- Corrected complex curvature operator, with `lapPsi` representing `Delta psi`. -/
noncomputable def thetaComplex
    (lapPsi psi : ℂ) (epsilon alpha : ℝ) : ℂ :=
  -lapPsi * complexRegularizedReciprocal psi epsilon alpha

/-- The modulus-squared part of the denominator is nonnegative. -/
theorem complex_normSq_nonnegative (psi : ℂ) :
    0 ≤ Complex.normSq psi := by
  exact Complex.normSq_nonneg psi

/-- M2/E17: the corrected denominator is strictly positive for every complex
field value whenever the regulator amplitude is positive. -/
theorem complexRegularizerDenominator_positive
    (psi : ℂ) (epsilon alpha : ℝ) (hepsilon : 0 < epsilon) :
    0 < complexRegularizerDenominator psi epsilon alpha := by
  unfold complexRegularizerDenominator
  have hnorm : 0 ≤ Complex.normSq psi := Complex.normSq_nonneg psi
  have hepsSq : 0 < epsilon ^ 2 := sq_pos_of_pos hepsilon
  have hexp : 0 < Real.exp (-2 * alpha * Complex.normSq psi) := Real.exp_pos _
  exact add_pos_of_nonneg_of_pos hnorm (mul_pos hepsSq hexp)

/-- The corrected denominator can therefore be used in a quotient globally. -/
theorem complexRegularizerDenominator_ne_zero
    (psi : ℂ) (epsilon alpha : ℝ) (hepsilon : 0 < epsilon) :
    complexRegularizerDenominator psi epsilon alpha ≠ 0 :=
  ne_of_gt (complexRegularizerDenominator_positive psi epsilon alpha hepsilon)

/-- M6B: the typed nonlinear curvature operator is exactly the canonical
modulus-squared quotient after reassociating multiplication and division. -/
theorem thetaComplex_canonical_formula
    (lapPsi psi : ℂ) (epsilon alpha : ℝ) :
    thetaComplex lapPsi psi epsilon alpha =
      (-lapPsi * star psi) /
        (complexRegularizerDenominator psi epsilon alpha : ℂ) := by
  simp only [thetaComplex, complexRegularizedReciprocal, div_eq_mul_inv]
  ring

/-- M6B: for positive regulator amplitude, the denominator occurring in the
canonical nonlinear operator is globally nonzero. -/
theorem thetaComplex_denominator_ne_zero
    (psi : ℂ) (epsilon alpha : ℝ) (hepsilon : 0 < epsilon) :
    (complexRegularizerDenominator psi epsilon alpha : ℂ) ≠ 0 := by
  exact_mod_cast
    complexRegularizerDenominator_ne_zero psi epsilon alpha hepsilon

/-- At a field node, the denominator is exactly `epsilon^2`, not zero. -/
@[simp] theorem complexRegularizerDenominator_at_zero
    (epsilon alpha : ℝ) :
    complexRegularizerDenominator 0 epsilon alpha = epsilon ^ 2 := by
  simp [complexRegularizerDenominator]

/-- The regularized reciprocal vanishes at a node while remaining defined. -/
@[simp] theorem complexRegularizedReciprocal_at_zero
    (epsilon alpha : ℝ) :
    complexRegularizedReciprocal 0 epsilon alpha = 0 := by
  simp [complexRegularizedReciprocal]

/-- Consequently the local curvature product vanishes when both the field and
its supplied Laplacian are zero. -/
@[simp] theorem thetaComplex_zero_state
    (epsilon alpha : ℝ) :
    thetaComplex 0 0 epsilon alpha = 0 := by
  simp [thetaComplex]

end WCTLean
