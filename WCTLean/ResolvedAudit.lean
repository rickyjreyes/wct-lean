import WCTLean.Models.CurvatureOperator

namespace WCTLean

/-- The first resolved audit module is intentionally minimal: E17 is compiled
through the library root before additional equation families are admitted. -/
theorem resolved_e17_counterexample :
    regularizedDenominator (-1) 1 0 = 0 :=
  regularizedDenominator_counterexample

end WCTLean
