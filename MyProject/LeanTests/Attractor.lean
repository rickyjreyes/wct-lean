import MyProject.Theta.Dynamics

namespace WCT

/-
  LEAN-2: Attractor uniqueness contract
-/

/--
  Unique attractor per Theta-parameter set.
-/
axiom Theta_unique_attractor_existsUnique :
  forall p : ThetaParams,
    ExistsUnique (fun s => IsAttractor p s)

end WCT
