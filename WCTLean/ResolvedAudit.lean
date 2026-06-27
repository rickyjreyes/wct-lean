import WCTLean.Models.CurvatureOperator
import WCTLean.Models.PhaseFlux
import WCTLean.Models.RestDensity
import WCTLean.Models.GhostModes
import WCTLean.Models.LogFlow
import WCTLean.Models.Collider

namespace WCTLean

/-- E9 continuity residual vanishes exactly when the local time derivative
balances the flux divergence. -/
theorem conservationResidual_zero_iff
    (duDt divFlux : ℝ) :
    conservationResidual duDt divFlux = 0 ↔ duDt = -divFlux := by
  unfold conservationResidual
  constructor <;> intro h <;> linarith

/-- E9 causal component bound from a nonnegative density and a bounded phase
speed. -/
theorem phaseFluxComponent_abs_le
    (energyDensity phaseGradientComponent c : ℝ)
    (henergy : 0 ≤ energyDensity)
    (hgradient : |phaseGradientComponent| ≤ c) :
    |phaseFluxComponent energyDensity phaseGradientComponent| ≤
      c * energyDensity := by
  unfold phaseFluxComponent
  rw [abs_mul, abs_of_nonneg henergy]
  have hmul := mul_le_mul_of_nonneg_left hgradient henergy
  nlinarith

/-- E2 domain condition: a strictly positive total density makes the weighted
average denominator nonzero. -/
theorem densityWeightedAverage_denominator_ne_zero
    {ι : Type*} [Fintype ι]
    (density : ι → ℝ)
    (htotal : 0 < ∑ i, density i) :
    (∑ i, density i) ≠ 0 :=
  ne_of_gt htotal

/-- E3 finite locking mismatch is nonnegative when every quadrature weight is
nonnegative. -/
theorem lockingMismatch_nonnegative
    {ι : Type*} [Fintype ι]
    (density phaseGradient sigma : ι → ℝ)
    (hdensity : ∀ i, 0 ≤ density i) :
    0 ≤ lockingMismatch density phaseGradient sigma := by
  unfold lockingMismatch
  exact Finset.sum_nonneg (fun i _ =>
    mul_nonneg (hdensity i) (sq_nonneg (phaseGradient i - sigma i)))

/-- G1 Gaussian detector-smearing factor is strictly positive. -/
theorem gaussianSmearingFactor_positive
    (logFrequency sigmaLog : ℝ) :
    0 < gaussianSmearingFactor logFrequency sigmaLog := by
  unfold gaussianSmearingFactor
  exact Real.exp_pos _

/-- The JUNO resolution proxy is always nonnegative as a real square root. -/
theorem junoResolution_nonnegative
    (a b energy : ℝ) :
    0 ≤ junoResolution a b energy := by
  unfold junoResolution
  exact Real.sqrt_nonneg _

/-- EX positive-domain closure: exponentiating the logarithmic field recovers
its positive input. -/
theorem exp_logField
    (psi : ℝ) (hpsi : 0 < psi) :
    Real.exp (logField psi) = psi := by
  simpa [logField] using Real.exp_log hpsi

/-- Collider logarithmic coordinate is invertible on the physical Q² > 0
domain. -/
theorem exp_logMomentum
    (qSquared : ℝ) (hq : 0 < qSquared) :
    Real.exp (logMomentum qSquared) = qSquared := by
  simpa [logMomentum] using Real.exp_log hq

end WCTLean
