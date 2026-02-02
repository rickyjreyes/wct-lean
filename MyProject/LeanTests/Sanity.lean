import MyProject.Theta.Definitions

namespace WCT

/-
  LEAN-0: Totality of Theta
-/

/--
  Theta is total: defined for every state.
-/
axiom Theta_total :
  forall (p : ThetaParams) (x : State),
    exists y : State, Theta p x = y

end WCT
