import MyProject.Theta.Entropy

namespace WCT

/-- Open entropy monotonicity obligation, not a theorem or axiom. -/
def EntropyMonotonicityObligation {S : Type} (M : ThetaModel S) : Prop :=
  ∀ p : ThetaParams, EntropyMonotoneTheta M p

end WCT
