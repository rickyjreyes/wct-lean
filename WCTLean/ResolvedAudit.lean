import WCTLean.Models.CurvatureOperator
import WCTLean.Models.PhaseFlux
import WCTLean.Models.RestDensity

namespace WCTLean

/-- E17 unrestricted-real counterexample. -/
theorem resolved_e17_counterexample :
    regularizedDenominator (-1) 1 0 = 0 :=
  regularizedDenominator_counterexample

/-- E9 local continuity equation written as an exact residual equivalence. -/
theorem conservationResidual_zero_iff
    (duDt divFlux : ℝ) :
    conservationResidual duDt divFlux = 0 ↔ duDt = -divFlux := by
  unfold conservationResidual
  constructor <;> intro h <;> linarith

/-- E2 domain condition: positive total density makes the weighted-average
denominator nonzero. -/
theorem densityWeightedAverage_denominator_ne_zero
    {ι : Type*} [Fintype ι]
    (density : ι → ℝ)
    (htotal : 0 < ∑ i, density i) :
    (∑ i, density i) ≠ 0 :=
  ne_of_gt htotal

/-- E3 finite locking mismatch is nonnegative under nonnegative quadrature
weights. -/
theorem lockingMismatch_nonnegative
    {ι : Type*} [Fintype ι]
    (density phaseGradient sigma : ι → ℝ)
    (hdensity : ∀ i, 0 ≤ density i) :
    0 ≤ lockingMismatch density phaseGradient sigma := by
  unfold lockingMismatch
  exact Finset.sum_nonneg (fun i _ =>
    mul_nonneg (hdensity i) (sq_nonneg (phaseGradient i - sigma i)))

end WCTLean
