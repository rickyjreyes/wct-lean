import MyProject.Theta.Entropy

namespace WCT

/-
  LEAN-1: Entropy monotonicity axiom
-/

/--
  WCT entropy monotonicity axiom.
  If this axiom fails, the theory is falsified.
-/
axiom Theta_entropy_monotone :
  forall p : ThetaParams,
    EntropyMonotoneTheta p

end WCT
