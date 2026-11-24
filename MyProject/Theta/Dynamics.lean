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

-- Theta_unique_attractor: removed assumed conclusion; no proof is claimed.

end WCT
