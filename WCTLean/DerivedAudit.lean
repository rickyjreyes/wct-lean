import Mathlib
import WCTLean.Energy
import WCTLean.Models.PhaseFlux

namespace WCTLean

/-!
# Derived audit batch 1

Kernel-checked algebraic consequences corresponding to the first promoted
`wct-sympy` derivation batch. Theorems here state their assumptions explicitly.
They do not claim global PDE well-posedness, variational existence, or empirical
validation.
-/

/-- E5: winding-based effective wavenumber. -/
noncomputable def effectiveWavenumber (n : ℤ) (loopLength : ℝ) : ℝ :=
  2 * Real.pi * |(n : ℝ)| / loopLength

/-- E5: constant-weight average of an integrated observable. -/
noncomputable def constantWeightedAverage
    (weight integratedObservable loopLength : ℝ) : ℝ :=
  (weight * integratedObservable) / (weight * loopLength)

/-- E5: exact loop closure identifies winding wavenumber with the ordinary
loop-average curvature rate. -/
theorem effectiveWavenumber_eq_loopAverage
    (n : ℤ) (loopLength loopCurvature : ℝ)
    (hclosure : loopCurvature = 2 * Real.pi * |(n : ℝ)|) :
    effectiveWavenumber n loopLength = loopCurvature / loopLength := by
  unfold effectiveWavenumber
  rw [hclosure]

/-- E5: a nonzero constant weight cancels from the weighted average. -/
theorem constantWeightedAverage_eq_loopAverage
    (weight integratedObservable loopLength : ℝ)
    (hweight : weight ≠ 0) :
    constantWeightedAverage weight integratedObservable loopLength =
      integratedObservable / loopLength := by
  unfold constantWeightedAverage
  by_cases hloop : loopLength = 0
  · simp [hloop]
  · field_simp [hweight, hloop]

/-- E5: exact closure and constant positive weight give the full algebraic
wavenumber chain used by the symbolic audit. -/
theorem resolved_e5_effectiveWavenumber_chain
    (n : ℤ) (weight loopLength loopCurvature : ℝ)
    (hweight : 0 < weight)
    (hclosure : loopCurvature = 2 * Real.pi * |(n : ℝ)|) :
    effectiveWavenumber n loopLength = loopCurvature / loopLength ∧
    constantWeightedAverage weight loopCurvature loopLength =
      loopCurvature / loopLength := by
  constructor
  · exact effectiveWavenumber_eq_loopAverage n loopLength loopCurvature hclosure
  · exact constantWeightedAverage_eq_loopAverage
      weight loopCurvature loopLength (ne_of_gt hweight)

/-- E9 algebraic core: polar decomposition gives
`star psi * dpsi = du/2 + i*u*dtheta`; its imaginary part is `u*dtheta`. -/
noncomputable def polarCurrentProduct (u du dtheta : ℝ) : ℂ :=
  (du / 2 : ℂ) + Complex.I * (u * dtheta : ℂ)

@[simp] theorem polarCurrentProduct_im (u du dtheta : ℝ) :
    (polarCurrentProduct u du dtheta).im = u * dtheta := by
  simp [polarCurrentProduct]

/-- E9: any field derivative satisfying the polar product factorization has
phase-current component `u*dtheta`. -/
theorem phaseCurrent_of_polar_factorization
    (psi dpsi : ℂ) (u du dtheta : ℝ)
    (hpolar : star psi * dpsi = polarCurrentProduct u du dtheta) :
    (star psi * dpsi).im = phaseFluxComponent u dtheta := by
  rw [hpolar]
  simp [phaseFluxComponent]

/-- E13/E14 Fourier-mode algebra: the real-space operator
`r - a*Delta - b*Delta^2` has one-mode symbol `r + a*k^2 - b*k^4`. -/
theorem bandpass_oneMode_symbol
    (r a b k amplitude : ℝ) :
    r * amplitude
      - a * (-k ^ 2 * amplitude)
      - b * (k ^ 4 * amplitude)
      = (r + a * k ^ 2 - b * k ^ 4) * amplitude := by
  ring

/-- E18: the two-term WCT energy skeleton is nonnegative under nonnegative
coefficients. -/
theorem resolved_e18_energy_nonnegative
    (c₁ c₂ gradientTerm curvatureTerm : ℝ)
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hgradient : 0 ≤ gradientTerm) (hcurvature : 0 ≤ curvatureTerm) :
    0 ≤ c₁ * gradientTerm + c₂ * curvatureTerm := by
  exact add_nonneg (mul_nonneg hc₁ hgradient) (mul_nonneg hc₂ hcurvature)

/-- E18 algebraic descent core: once the chain rule identifies the energy
rate with minus a squared gradient norm, the rate is nonpositive. -/
theorem resolved_e18_gradientFlow_descent
    (variationNormSq energyRate : ℝ)
    (hnorm : 0 ≤ variationNormSq)
    (hchain : energyRate = -variationNormSq) :
    energyRate ≤ 0 := by
  rw [hchain]
  exact neg_nonpos.mpr hnorm

/-- E58 band-selective denominator. -/
def bandGreenDenominator (r a k kStar : ℝ) : ℝ :=
  r + a * (k ^ 2 - kStar ^ 2) ^ 2

/-- E58 Green kernel. -/
noncomputable def bandGreenKernel (r a k kStar : ℝ) : ℝ :=
  1 / bandGreenDenominator r a k kStar

/-- E58: positive offset and nonnegative shell coefficient make the denominator
strictly positive. -/
theorem bandGreenDenominator_pos
    (r a k kStar : ℝ) (hr : 0 < r) (ha : 0 ≤ a) :
    0 < bandGreenDenominator r a k kStar := by
  unfold bandGreenDenominator
  exact add_pos_of_pos_of_nonneg hr (mul_nonneg ha (sq_nonneg _))

/-- E58: the shell denominator is bounded below by `r`. -/
theorem bandGreenDenominator_ge_offset
    (r a k kStar : ℝ) (ha : 0 ≤ a) :
    r ≤ bandGreenDenominator r a k kStar := by
  unfold bandGreenDenominator
  exact le_add_of_nonneg_right (mul_nonneg ha (sq_nonneg _))

/-- E58: the Green kernel is strictly positive. -/
theorem bandGreenKernel_pos
    (r a k kStar : ℝ) (hr : 0 < r) (ha : 0 ≤ a) :
    0 < bandGreenKernel r a k kStar := by
  unfold bandGreenKernel
  exact one_div_pos.mpr (bandGreenDenominator_pos r a k kStar hr ha)

/-- E58: the kernel is globally bounded above by `1/r`. -/
theorem bandGreenKernel_le_inverseOffset
    (r a k kStar : ℝ) (hr : 0 < r) (ha : 0 ≤ a) :
    bandGreenKernel r a k kStar ≤ 1 / r := by
  unfold bandGreenKernel
  exact one_div_le_one_div_of_le hr
    (bandGreenDenominator_ge_offset r a k kStar ha)

/-- E58: the upper bound is attained on the selected shell. -/
@[simp] theorem bandGreenKernel_at_shell
    (r a kStar : ℝ) :
    bandGreenKernel r a kStar kStar = 1 / r := by
  simp [bandGreenKernel, bandGreenDenominator]

/-- CM9 photon oscillator equation. -/
def PhotonSecondOrderMode
    (acceleration cSoundSq k delta potential : ℝ) : Prop :=
  acceleration + cSoundSq * k ^ 2 * delta = -k ^ 2 * potential

/-- CM9 photon first-order acceleration equation. -/
def PhotonFirstOrderAcceleration
    (velocityRate cSoundSq k delta potential : ℝ) : Prop :=
  velocityRate = -cSoundSq * k ^ 2 * delta - k ^ 2 * potential

/-- CM9: the photon second-order equation and first-order acceleration equation
are algebraically equivalent after identifying velocity rate with acceleration. -/
theorem photonSecondOrder_iff_firstOrder
    (acceleration cSoundSq k delta potential : ℝ) :
    PhotonSecondOrderMode acceleration cSoundSq k delta potential ↔
    PhotonFirstOrderAcceleration acceleration cSoundSq k delta potential := by
  unfold PhotonSecondOrderMode PhotonFirstOrderAcceleration
  constructor <;> intro h <;> linarith

/-- CM9 baryon oscillator equation. -/
def BaryonSecondOrderMode
    (acceleration compression cSoundSq k photonDelta potential : ℝ) : Prop :=
  acceleration + compression * cSoundSq * k ^ 2 * photonDelta =
    -k ^ 2 * potential

/-- CM9 baryon first-order acceleration equation. -/
def BaryonFirstOrderAcceleration
    (velocityRate compression cSoundSq k photonDelta potential : ℝ) : Prop :=
  velocityRate =
    -compression * cSoundSq * k ^ 2 * photonDelta - k ^ 2 * potential

/-- CM9: the baryon second-order and first-order acceleration forms are
algebraically equivalent. -/
theorem baryonSecondOrder_iff_firstOrder
    (acceleration compression cSoundSq k photonDelta potential : ℝ) :
    BaryonSecondOrderMode acceleration compression cSoundSq k photonDelta potential ↔
    BaryonFirstOrderAcceleration acceleration compression cSoundSq k photonDelta potential := by
  unfold BaryonSecondOrderMode BaryonFirstOrderAcceleration
  constructor <;> intro h <;> linarith

/-- CM12: dimensionless power-spectrum observable. -/
noncomputable def dimensionlessPowerSpectrum (k power : ℝ) : ℝ :=
  k ^ 3 * power / (2 * Real.pi ^ 2)

/-- CM13: second-to-first peak power ratio. -/
noncomputable def peakPowerRatio21 (power₁ power₂ : ℝ) : ℝ := power₂ / power₁

/-- CM13: third-to-first peak power ratio. -/
noncomputable def peakPowerRatio31 (power₁ power₃ : ℝ) : ℝ := power₃ / power₁

/-- CM13: second-to-first peak wavenumber ratio. -/
noncomputable def peakScaleRatio21 (k₁ k₂ : ℝ) : ℝ := k₂ / k₁

/-- CM13: third-to-first peak wavenumber ratio. -/
noncomputable def peakScaleRatio31 (k₁ k₃ : ℝ) : ℝ := k₃ / k₁

/-- CM16: horizon wavenumber from a supplied horizon radius. -/
noncomputable def horizonWavenumber (horizonRadius : ℝ) : ℝ :=
  2 * Real.pi / horizonRadius

end WCTLean
