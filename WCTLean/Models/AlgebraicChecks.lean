import Mathlib

namespace WCTLean

/-!
# Canonical algebraic checks

This module collects finite-dimensional or scalar consequences that can be
kernel-checked without claiming the unresolved functional-analysis or physical
bridges of the corresponding equations.
-/

/-- E20 quadratic cavity sector. -/
def cavityQuadratic (kappa theta gamma S P : ℝ) : ℝ :=
  kappa * S ^ 2 + theta * P ^ 2 - gamma * S * P

/-- E20: positive `kappa` and a nonnegative determinant make the quadratic
sector nonnegative. -/
theorem cavityQuadratic_nonnegative
    (kappa theta gamma S P : ℝ)
    (hkappa : 0 < kappa) (_htheta : 0 ≤ theta)
    (hdet : gamma ^ 2 ≤ 4 * kappa * theta) :
    0 ≤ cavityQuadratic kappa theta gamma S P := by
  have hsquare : 0 ≤ (2 * kappa * S - gamma * P) ^ 2 := sq_nonneg _
  have htail : 0 ≤ (4 * kappa * theta - gamma ^ 2) * P ^ 2 :=
    mul_nonneg (sub_nonneg.mpr hdet) (sq_nonneg _)
  have hid :
      4 * kappa * cavityQuadratic kappa theta gamma S P =
        (2 * kappa * S - gamma * P) ^ 2 +
          (4 * kappa * theta - gamma ^ 2) * P ^ 2 := by
    unfold cavityQuadratic
    ring
  have hscaled : 0 ≤ 4 * kappa * cavityQuadratic kappa theta gamma S P := by
    rw [hid]
    exact add_nonneg hsquare htail
  nlinarith

/-- E28 scalar alpha-drop expression. -/
noncomputable def alphaDropValue (logRetainedSum beta n : ℝ) : ℝ :=
  1 + logRetainedSum / n + beta

/-- E28: the corrected beta inequality is sufficient for alpha-drop below one. -/
theorem alphaDrop_lt_one
    (logRetainedSum beta n : ℝ)
    (hbeta : beta < -logRetainedSum / n) :
    alphaDropValue logRetainedSum beta n < 1 := by
  rw [neg_div] at hbeta
  unfold alphaDropValue
  linarith

/-- E29 one-step entropy-pruning upper bound. -/
noncomputable def entropyPrunedUpperBound (modeCount entropyDrop : ℝ) : ℝ :=
  Real.exp (-entropyDrop) * modeCount

/-- E33: exponentiating `H ≤ log K` gives the corrected support inequality
`exp H ≤ K` for positive support size. -/
theorem exp_entropy_le_support
    (entropy supportSize : ℝ)
    (hsupport : 0 < supportSize)
    (hentropy : entropy ≤ Real.log supportSize) :
    Real.exp entropy ≤ supportSize := by
  calc
    Real.exp entropy ≤ Real.exp (Real.log supportSize) :=
      Real.exp_le_exp.mpr hentropy
    _ = supportSize := Real.exp_log hsupport

/-- E45 corrected quality factor using loss power. -/
noncomputable def effectiveQualityFactor
    (omega storedEnergy lossPower : ℝ) : ℝ :=
  omega * storedEnergy / lossPower

/-- E45: positive frequency, stored energy, and loss power give positive Q. -/
theorem effectiveQualityFactor_positive
    (omega storedEnergy lossPower : ℝ)
    (homega : 0 < omega) (henergy : 0 < storedEnergy)
    (hloss : 0 < lossPower) :
    0 < effectiveQualityFactor omega storedEnergy lossPower := by
  unfold effectiveQualityFactor
  exact div_pos (mul_pos homega henergy) hloss

/-- E47 dynamical power-balance residual. -/
def powerBalanceResidual
    (energyRate powerIn powerFusion powerLoss powerOut : ℝ) : ℝ :=
  energyRate - (powerIn + powerFusion - powerLoss - powerOut)

/-- E47: zero energy rate and exact balance are equivalent to source power
equaling sink power. -/
theorem stationaryPowerBalance_iff
    (powerIn powerFusion powerLoss powerOut : ℝ) :
    powerBalanceResidual 0 powerIn powerFusion powerLoss powerOut = 0 ↔
      powerIn + powerFusion = powerLoss + powerOut := by
  unfold powerBalanceResidual
  constructor <;> intro h <;> linarith

/-- E49 corrected effective mass-squared definition from a frequency gap. -/
noncomputable def effectiveMassSqFromGap
    (hbar c frequencyGap : ℝ) : ℝ :=
  hbar ^ 2 / c ^ 4 * frequencyGap

/-- E49 is exact by the corrected definition. -/
@[simp] theorem effectiveMassSqFromGap_eq
    (hbar c frequencyGap : ℝ) :
    effectiveMassSqFromGap hbar c frequencyGap =
      hbar ^ 2 / c ^ 4 * frequencyGap := rfl

/-- E51 scalar component of the curvature-gradient commutator. -/
noncomputable def curvatureGradientCommutator
    (lapPsi gradLapPsi denominator gradDenominator : ℝ) : ℝ :=
  (-(gradLapPsi * denominator - lapPsi * gradDenominator) /
      denominator ^ 2) - (-gradLapPsi / denominator)

/-- E51: quotient-rule expansion leaves exactly the denominator-gradient term. -/
theorem curvatureGradientCommutator_eq
    (lapPsi gradLapPsi denominator gradDenominator : ℝ)
    (hden : denominator ≠ 0) :
    curvatureGradientCommutator lapPsi gradLapPsi denominator gradDenominator =
      lapPsi * gradDenominator / denominator ^ 2 := by
  unfold curvatureGradientCommutator
  field_simp [hden]
  ring

/-- E53 local curvature pressure contribution. -/
def curvaturePressureDensity (c2 thetaNormSq : ℝ) : ℝ :=
  c2 * thetaNormSq

/-- E53: nonnegative coefficient and norm-square give nonnegative pressure. -/
theorem curvaturePressureDensity_nonnegative
    (c2 thetaNormSq : ℝ) (hc2 : 0 ≤ c2) (htheta : 0 ≤ thetaNormSq) :
    0 ≤ curvaturePressureDensity c2 thetaNormSq :=
  mul_nonneg hc2 htheta

/-- E59 coordinate mask representing projection onto a fixed spectral annulus. -/
def maskProjection {ι α : Type*} [Zero α]
    (keep : ι → Bool) (amplitude : ι → α) : ι → α :=
  fun i => if keep i = true then amplitude i else 0

/-- E59: applying the same fixed annular mask twice is idempotent. -/
theorem maskProjection_idempotent
    {ι α : Type*} [Zero α]
    (keep : ι → Bool) (amplitude : ι → α) :
    maskProjection keep (maskProjection keep amplitude) =
      maskProjection keep amplitude := by
  funext i
  cases h : keep i <;> simp [maskProjection, h]

/-- E62 scalar spectral-energy fraction. -/
noncomputable def spectralEnergyFraction
    (annularEnergy totalEnergy : ℝ) : ℝ :=
  annularEnergy / totalEnergy

/-- E62: a nonnegative partial energy bounded by a positive total energy gives
a fraction in `[0,1]`. -/
theorem spectralEnergyFraction_mem_unitInterval
    (annularEnergy totalEnergy : ℝ)
    (hannular : 0 ≤ annularEnergy)
    (htotal : 0 < totalEnergy)
    (hle : annularEnergy ≤ totalEnergy) :
    0 ≤ spectralEnergyFraction annularEnergy totalEnergy ∧
      spectralEnergyFraction annularEnergy totalEnergy ≤ 1 := by
  constructor
  · exact div_nonneg hannular (le_of_lt htotal)
  · exact (div_le_one htotal).2 hle

/-- E81 spectral second-moment coherence length. -/
noncomputable def spectralCoherenceLength (secondMoment : ℝ) : ℝ :=
  secondMoment ^ (-(1 : ℝ) / 2)

/-- E81 gradient-ratio coherence length. -/
noncomputable def gradientCoherenceLength
    (l2Norm gradientL2Norm : ℝ) : ℝ :=
  l2Norm / gradientL2Norm

end WCTLean
