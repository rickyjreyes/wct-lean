import MyProject.Theta.Entropy

namespace WCT

/-
  Explicit falsification contract for WCT
-/

/--
  WCT is falsified if ANY of the following occur:
  1. Entropy increases under Theta for some parameter set
  2. Multiple attractors exist for the same Theta
-/
def WCT_Falsified : Prop :=
  (exists p : ThetaParams, Not (EntropyMonotoneTheta p))
  \/
  (exists p : ThetaParams,
    exists s1 s2 : State,
      Ne s1 s2 /\
      IsAttractor p s1 /\
      IsAttractor p s2)

end WCT
