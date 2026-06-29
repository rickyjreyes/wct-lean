import Mathlib

namespace WCTLean

/-!
# Unified operator skeleton

The corrected M6A/M7 convention uses a negative fourth-order shell term
`-c2 (Delta + kStar^2)^2` with `c2 > 0`.
-/

/-- Corrected fourth-order shell contribution. -/
def unifiedShellTerm (c2 laplaceSymbol kStarSq : ℝ) : ℝ :=
  -c2 * (laplaceSymbol + kStarSq) ^ 2

/-- M6A linear Fourier-symbol skeleton with corrected ultraviolet sign. -/
def unifiedLinearSymbol
    (c1 c2 c3 c4 laplaceSymbol sigmaSq kStarSq winding radius scalingExponent : ℝ) : ℂ :=
  (c1 * (laplaceSymbol + sigmaSq) +
    unifiedShellTerm c2 laplaceSymbol kStarSq +
    c4 * Real.rpow radius (-scalingExponent) : ℝ) +
    Complex.I * (c3 * winding)

/-- Positive `c2` makes the fourth-order shell term nonpositive. -/
theorem unifiedShellTerm_nonpositive
    (c2 laplaceSymbol kStarSq : ℝ) (hc2 : 0 ≤ c2) :
    unifiedShellTerm c2 laplaceSymbol kStarSq ≤ 0 := by
  unfold unifiedShellTerm
  exact neg_nonpos.mpr (mul_nonneg hc2 (sq_nonneg _))

/-- The shell contribution is zero on the represented Fourier shell. -/
theorem unifiedShellTerm_zero_on_shell
    (c2 laplaceSymbol kStarSq : ℝ)
    (hshell : laplaceSymbol + kStarSq = 0) :
    unifiedShellTerm c2 laplaceSymbol kStarSq = 0 := by
  simp [unifiedShellTerm, hshell]

def unifiedRealVectorField
    (thetaTerm cubicTerm helmholtzTerm shellTerm dimensionalTerm stochasticTerm : ℝ) : ℝ :=
  thetaTerm + cubicTerm + helmholtzTerm + shellTerm + dimensionalTerm + stochasticTerm

structure UnifiedCoefficients where
  nonlinear : ℝ
  helmholtz : ℝ
  shell : ℝ
  winding : ℝ
  dimensional : ℝ
  stochastic : ℝ

end WCTLean
