import MyProject.Theta.Entropy

namespace WCT

/-- Model-specific falsification criteria. The absence of these counterexamples
is not established here and would not establish all physical claims of WCT. -/
def WCT_Falsified {S : Type} [MetricSpace S] (M : ThetaModel S) : Prop :=
  (∃ p : ThetaParams, ¬ EntropyMonotoneTheta M p) ∨
  (∃ (p : ThetaParams) (s1 s2 : S),
    s1 ≠ s2 ∧ IsAttractor (M.step p) s1 ∧ IsAttractor (M.step p) s2)

end WCT
