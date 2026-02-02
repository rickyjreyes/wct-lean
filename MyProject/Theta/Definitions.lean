import MyProject.Theta.Core

namespace WCT

/-
  Core Theta axioms
-/

-- Theta is nontrivial
axiom Theta_nontrivial :
  forall p : ThetaParams,
    exists s : State, Ne (Theta p s) s

-- Theta is deterministic
axiom Theta_deterministic :
  forall (p : ThetaParams) (s1 s2 : State),
    s1 = s2 -> Theta p s1 = Theta p s2

-- Theta is many-to-one (nonlinear)
axiom Theta_nonlinear :
  forall p : ThetaParams,
    exists s1 s2 : State,
      Ne s1 s2 /\ Theta p s1 = Theta p s2

-- Attractor existence
axiom attractor_exists :
  forall p : ThetaParams,
    exists s : State, IsAttractor p s

-- Attractor uniqueness
axiom attractor_unique :
  forall (p : ThetaParams) (s1 s2 : State),
    IsAttractor p s1 ->
    IsAttractor p s2 ->
    s1 = s2

end WCT
