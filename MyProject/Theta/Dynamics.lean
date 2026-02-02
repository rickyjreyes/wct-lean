import MyProject.Theta.Definitions

namespace WCT

/-
  Attractor dynamics
-/

/--
  Uniqueness of the attractor for each fixed Theta-parameter set.
-/
def UniqueAttractor (p : ThetaParams) : Prop :=
  forall x y : State,
    IsAttractor p x ->
    IsAttractor p y ->
    x = y

/--
  For every Theta-parameter set,
  there exists exactly one curvature-locked state.
-/
axiom Theta_unique_attractor :
  forall p : ThetaParams,
    exists s : State, IsAttractor p s /\ UniqueAttractor p

end WCT
