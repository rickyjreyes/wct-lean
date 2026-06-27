import Mathlib

namespace WCTLean

/-- E17 scalar denominator for the regularized curvature operator. -/
noncomputable def regularizedDenominator
    (psi epsilon alpha : ℝ) : ℝ :=
  psi + epsilon * Real.exp (-alpha * psi ^ 2)

/-- E17 scalarized curvature operator; `lapPsi` represents Δψ. -/
noncomputable def thetaScalar
    (lapPsi psi epsilon alpha : ℝ) : ℝ :=
  -lapPsi / regularizedDenominator psi epsilon alpha

/-- Exact counterexample: the printed regularizer does not guarantee a
nonzero denominator for unrestricted real fields. -/
@[simp] theorem regularizedDenominator_counterexample :
    regularizedDenominator (-1) 1 0 = 0 := by
  simp [regularizedDenominator]

/-- Corrected admissible sector: if ψ is nonnegative and ε is positive, the
regularized denominator is strictly positive for every real α. -/
theorem regularizedDenominator_positive
    (psi epsilon alpha : ℝ)
    (hpsi : 0 ≤ psi) (hepsilon : 0 < epsilon) :
    0 < regularizedDenominator psi epsilon alpha := by
  unfold regularizedDenominator
  have hexp : 0 < Real.exp (-alpha * psi ^ 2) := Real.exp_pos _
  have hreg : 0 < epsilon * Real.exp (-alpha * psi ^ 2) :=
    mul_pos hepsilon hexp
  linarith

/-- The corrected admissible sector makes the curvature quotient well-defined. -/
theorem regularizedDenominator_ne_zero
    (psi epsilon alpha : ℝ)
    (hpsi : 0 ≤ psi) (hepsilon : 0 < epsilon) :
    regularizedDenominator psi epsilon alpha ≠ 0 :=
  ne_of_gt (regularizedDenominator_positive psi epsilon alpha hpsi hepsilon)

end WCTLean
