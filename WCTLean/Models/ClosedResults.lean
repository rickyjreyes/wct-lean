import Mathlib
import WCTLean.Models.Locking

namespace WCTLean

/-!
# Closed algebraic results from the WCT closure audit

These theorems close narrow mathematical obligations. They do not assert
existence or orbital stability of a solution of the full WCT PDE, nor do they
establish a physical mass, gauge, gravity, or cosmology model.
-/

/-- The corrected modulus-squared denominator is strictly positive for ε > 0. -/
theorem correctedDenominator_pos
    (z : ℂ) (ε α : ℝ) (hε : 0 < ε) :
    0 < Complex.normSq z + ε ^ 2 * Real.exp (-2 * α * Complex.normSq z) := by
  have hε2 : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hexp : 0 < Real.exp (-2 * α * Complex.normSq z) := Real.exp_pos _
  have hterm : 0 < ε ^ 2 * Real.exp (-2 * α * Complex.normSq z) :=
    mul_pos hε2 hexp
  exact add_pos_of_nonneg_of_pos (Complex.normSq_nonneg z) hterm

/-- A smooth scalar phase gradient has zero Abelian field strength whenever
mixed derivatives commute. -/
theorem scalarPhase_pureGauge
    (∂μ∂νθ ∂ν∂μθ q : ℝ) (hq : q ≠ 0)
    (hcomm : ∂μ∂νθ = ∂ν∂μθ) :
    (∂μ∂νθ - ∂ν∂μθ) / q = 0 := by
  rw [hcomm]
  simp

/-- Exact phase-curvature locking is equivalent to zero winding mismatch in
its scalar closure equation. -/
theorem exactLock_iff_zeroMismatch
    (winding : ℤ) (integratedSigma : ℝ) :
    integratedSigma = 2 * Real.pi * (winding : ℝ) ↔
      2 * Real.pi * (winding : ℝ) - integratedSigma = 0 := by
  constructor <;> intro h
  · linarith
  · linarith

/-- Algebraic winding correction to a conditional mass law. -/
theorem correctedMassLaw
    (ℏ c geometricK correction : ℝ) (hc : c ≠ 0) :
    (ℏ / c) * (geometricK + correction) =
      (ℏ / c) * geometricK + (ℏ / c) * correction := by
  ring

/-- The logarithmic frequency k and discrete scaling ratio λ = exp(2π/k)
obey log λ = 2π/k for nonzero k. -/
theorem log_discreteScaleRatio
    (k : ℝ) (hk : k ≠ 0) :
    Real.log (Real.exp (2 * Real.pi / k)) = 2 * Real.pi / k := by
  exact Real.log_exp _

/-- The discrete scaling ratio associated with a real logarithmic frequency
is strictly positive. -/
theorem discreteScaleRatio_pos (k : ℝ) :
    0 < Real.exp (2 * Real.pi / k) := Real.exp_pos _

end WCTLean
