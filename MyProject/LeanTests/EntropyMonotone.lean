import MyProject.Theta.Entropy

namespace WCT

/-- LEAN-1: open monotonicity obligation, not a theorem of the abstract data. -/
def Theta_entropy_monotone (M : ThetaModel) : Prop :=
  ∀ p : ThetaParams, EntropyMonotoneTheta M p

end WCT
