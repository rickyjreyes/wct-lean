/-
  WCTLean/Main.lean

  Root import for the WCT Lean foundation and resolved equation audit.
-/

import WCTLean.Dimension
import WCTLean.Curvature
import WCTLean.Energy
import WCTLean.Koide
import WCTLean.Fourier
import WCTLean.ResolvedAudit

namespace WCTLean

/-- A bundled smoke test that references the dimensional mass lemma. -/
theorem wctlean_smoke :
    mulDim (divDim actionDim velocityDim) inverseLengthDim = massDim :=
  hbar_div_c_mul_k_is_mass

end WCTLean
