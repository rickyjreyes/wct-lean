import MyProject.Theta.Entropy

namespace WCT

/-- The original falsification alternatives, for explicitly supplied model data.
The fixed-point predicate is unchanged; no physical stability is inferred. -/
def WCT_Falsified (M : ThetaModel) : Prop :=
  (∃ p : ThetaParams, ¬ EntropyMonotoneTheta M p) ∨
  (∃ p : ThetaParams, ∃ s1 s2 : M.State,
    s1 ≠ s2 ∧ IsAttractor M p s1 ∧ IsAttractor M p s2)

end WCT
