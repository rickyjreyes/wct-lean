import MyProject.Theta.Entropy
import MyProject.Theta.Baselines
import MyProject.LeanTests.DimensionFailure

namespace WCT

/-- The original falsification alternatives, for explicitly supplied model data.
The fixed-point predicate is unchanged; no physical stability is inferred. -/
def LegacyFixedPointContractFalsified (M : ThetaModel) : Prop :=
  (∃ p : ThetaParams, ¬ EntropyMonotoneTheta M p) ∨
  (∃ p : ThetaParams, ∃ s1 s2 : M.State,
    s1 ≠ s2 ∧ IsFixedPoint M p s1 ∧ IsFixedPoint M p s2)


/-- All four alternatives promised by the initial README. This is a
model-relative falsification predicate, not a validity theorem. Connecting
the supplied maps and admissibility predicates to the actual physical model
remains open. The original two-alternative contract is retained above. -/
def FullContractFalsified (M : ThetaModel) [MetricSpace M.State]
    [AddCommGroup M.State] [Module ℝ M.State]
    (B : BaselineModel M) (D : DimensionIndexedModel) : Prop :=
  (∃ p : ThetaParams, ¬ EntropyMonotoneTheta M p) ∨
  (∃ p : ThetaParams, ¬ ∃! s : M.State, IsAttractingFixedPoint M p s) ∨
  ¬ dimensionRestrictionObligation D ∨
  ¬ Theta_nonlinear M ∨ ¬ Theta_not_baseline M B

end WCT
