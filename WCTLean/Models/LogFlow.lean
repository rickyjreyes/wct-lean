import Mathlib

namespace WCTLean

noncomputable def logField (psi : ℝ) : ℝ := Real.log psi

def logCurvatureResidual (uTime lapU gradUSq : ℝ) : ℝ :=
  uTime - (lapU + gradUSq)

def diffusionResidual (psiTime lapPsi : ℝ) : ℝ := psiTime - lapPsi

def FilamentLocalizationCondition (logGradientNorm curvature : ℝ) : Prop :=
  logGradientNorm = curvature

theorem exp_chain_rule_algebra (u uPrime : ℝ) :
    Real.exp u * uPrime = uPrime * Real.exp u := by ring

end WCTLean
