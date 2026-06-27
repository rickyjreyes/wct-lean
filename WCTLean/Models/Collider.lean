import Mathlib
import WCTLean.Models.GhostModes

namespace WCTLean

noncomputable def logMomentum (qSquared : ℝ) : ℝ := Real.log qSquared

def activeDomainWinding (frequency domainWidth : ℝ) : ℝ :=
  frequency * domainWidth / (2 * Real.pi)

structure ColliderFitEvidence where
  deltaChiSq : ℝ
  nullPValue : ℝ
  phaseCoherent : Bool
  covarianceAvailable : Bool

end WCTLean
