import MyProject.Theta.Definitions

namespace WCT

/-
  Entropy monotonicity contract
-/

/--
  Entropy is monotone under one application of Theta.
-/
def EntropyMonotoneTheta (p : ThetaParams) : Prop :=
  forall s : State,
    Entropy (Theta p s) <= Entropy s

-- Abstract flow on states
axiom Flow : Type

-- Flow evaluation
axiom evalFlow : Flow -> State -> Real -> State

/--
  Entropy is monotone along a flow trajectory.
-/
def EntropyMonotoneFlow (H : State -> Real) (Phi : Flow) : Prop :=
  forall (x : State) (t1 t2 : Real),
    t1 <= t2 ->
    H (evalFlow Phi x t2) <= H (evalFlow Phi x t1)

end WCT
