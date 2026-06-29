import Mathlib

namespace WCTLean

/-- EX logarithmic field representation on the positive real sector. -/
noncomputable def logField (psi : ℝ) : ℝ := Real.log psi

/-- EX: exponentiation recovers the original positive field value. -/
theorem exp_logField_eq
    (psi : ℝ) (hpsi : 0 < psi) :
    Real.exp (logField psi) = psi := by
  simp [logField, Real.exp_log hpsi]

/-- EY residual for the logarithmic curvature-flow equation. -/
def logCurvatureResidual (uTime lapU gradUSq : ℝ) : ℝ :=
  uTime - (lapU + gradUSq)

/-- EZ residual for the linear diffusion equation after Cole-Hopf substitution. -/
def diffusionResidual (psiTime lapPsi : ℝ) : ℝ := psiTime - lapPsi

/-- EY/EZ: under the supplied temporal and Laplacian chain rules, the diffusion
residual factors as the field value times the logarithmic residual. -/
theorem coleHopf_residual_factorization
    (psi psiTime lapPsi uTime lapU gradUSq : ℝ)
    (htime : psiTime = psi * uTime)
    (hlap : lapPsi = psi * (lapU + gradUSq)) :
    diffusionResidual psiTime lapPsi =
      psi * logCurvatureResidual uTime lapU gradUSq := by
  rw [htime, hlap]
  unfold diffusionResidual logCurvatureResidual
  ring

/-- EY/EZ: on a nonzero field sector, the linear diffusion residual vanishes
exactly when the logarithmic curvature residual vanishes, provided the chain
rules hold. -/
theorem diffusionResidual_zero_iff_logCurvatureResidual_zero
    (psi psiTime lapPsi uTime lapU gradUSq : ℝ)
    (hpsi : psi ≠ 0)
    (htime : psiTime = psi * uTime)
    (hlap : lapPsi = psi * (lapU + gradUSq)) :
    diffusionResidual psiTime lapPsi = 0 ↔
      logCurvatureResidual uTime lapU gradUSq = 0 := by
  rw [coleHopf_residual_factorization
    psi psiTime lapPsi uTime lapU gradUSq htime hlap]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hzero | hres
    · exact (hpsi hzero).elim
    · exact hres
  · intro hres
    rw [hres, mul_zero]

/-- FA filament-localization condition. -/
def FilamentLocalizationCondition (logGradientNorm curvature : ℝ) : Prop :=
  logGradientNorm = curvature

/-- FA scalar mismatch associated with the localization condition. -/
def filamentLocalizationMismatch
    (logGradientNorm curvature : ℝ) : ℝ :=
  logGradientNorm - curvature

/-- FA: exact filament localization is equivalent to zero scalar mismatch. -/
theorem filamentLocalizationCondition_iff_mismatch_zero
    (logGradientNorm curvature : ℝ) :
    FilamentLocalizationCondition logGradientNorm curvature ↔
      filamentLocalizationMismatch logGradientNorm curvature = 0 := by
  unfold FilamentLocalizationCondition filamentLocalizationMismatch
  constructor <;> intro h <;> linarith

/-- Elementary algebra used in the exponential chain rule. -/
theorem exp_chain_rule_algebra (u uPrime : ℝ) :
    Real.exp u * uPrime = uPrime * Real.exp u := by
  ring

end WCTLean
