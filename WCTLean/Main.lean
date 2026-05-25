/-
  WCTLean/Main.lean

  Root import for the narrow WCT Lean foundation.
-/

import WCTLean.Dimension
import WCTLean.Curvature
import WCTLean.Energy
import WCTLean.Koide
import WCTLean.Fourier

namespace WCTLean

/-- A bundled "smoke test" that just references the headline lemmas so the
    library has a single point of entry. -/
theorem wctlean_smoke :
    mulDim (divDim actionDim velocityDim) inverseLengthDim = massDim :=
  hbar_div_c_mul_k_is_mass

end WCTLean
