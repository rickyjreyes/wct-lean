import WCTLean.Models.CurvatureOperator
import WCTLean.Models.PhaseFlux

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

end WCTLean
