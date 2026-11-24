import MyProject.Theta.Entropy

namespace WCT

/-- The original falsification alternatives, for explicitly supplied model data.
The fixed-point predicate is unchanged; no physical stability is inferred. -/
def LegacyFixedPointContractFalsified (M : ThetaModel) : Prop :=
  (∃ p : ThetaParams, ¬ EntropyMonotoneTheta M p) ∨
  (∃ p : ThetaParams, ∃ s1 s2 : M.State,
    s1 ≠ s2 ∧ IsFixedPoint M p s1 ∧ IsFixedPoint M p s2)

end WCT
