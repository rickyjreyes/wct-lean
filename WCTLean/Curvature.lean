/-
  WCTLean/Curvature.lean

  Curvature and torsion live at inverse-length dimension.
  We define a dimensional square-root that is total (returns `Option Dim`)
  and only succeeds when every exponent is even.
-/

import WCTLean.Dimension

namespace WCTLean

/-- Curvature dimension. -/
def kappaDim : Dim := inverseLengthDim

/-- Torsion dimension. -/
def tauDim : Dim := inverseLengthDim

/-- Partial dimensional square root: defined only when every integer
    exponent is even. -/
def sqrtDim (d : Dim) : Option Dim :=
  if d.m % 2 = 0 ∧ d.l % 2 = 0 ∧ d.t % 2 = 0 then
    some ⟨d.m / 2, d.l / 2, d.t / 2⟩
  else
    none

/-- `κ² + τ²` has dimension `L⁻²`. We model the *dimensional* part:
    both summands have the same dimension `L⁻²`, so the sum does too. -/
theorem kappa_sq_dim :
    mulDim kappaDim kappaDim = ⟨0, -2, 0⟩ := by
  decide

theorem tau_sq_dim :
    mulDim tauDim tauDim = ⟨0, -2, 0⟩ := by
  decide

/-- `√(L⁻²) = L⁻¹` at the dimensional level. -/
theorem sqrt_inverse_length_squared :
    sqrtDim (mulDim inverseLengthDim inverseLengthDim) = some inverseLengthDim := by
  decide

/-- The combined curvature magnitude `√(κ² + τ²)` lives at inverse-length
    dimension, captured at the dimensional level via `sqrtDim`. -/
theorem sqrt_kappa_sq_dim :
    sqrtDim (mulDim kappaDim kappaDim) = some inverseLengthDim := by
  decide

end WCTLean
