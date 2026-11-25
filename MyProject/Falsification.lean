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


/-- Unified model-relative diagnostic. The local state, map and functionals
are projections of D, so unrelated maps cannot be mixed. No physical
realization or validity is certified. The baseline class is compared only
at the designated positive dimension; full physical scope remains OPEN. -/
def FullContractFalsified (D : DimensionIndexedModel) (d : Nat) (hd : 0 < d)
    [AddCommGroup (D.State d)] [Module ℝ (D.State d)]
    (B : BaselineModel (dimensionSlice D d hd)) : Prop :=
  (∃ (j : Nat), 0 < j ∧ ∃ p : ThetaParams, ∃ x : D.State j,
    D.admissible j x ∧ D.entropy j (D.Theta j p x) > D.entropy j x) ∨
  ¬ dimensionRestrictionObligation D ∨
  ¬ Theta_nonlinear (dimensionSlice D d hd) ∨
  ¬ Theta_not_baseline (dimensionSlice D d hd) B ∨
  ¬ ExcludesLinearBaselines (dimensionSlice D d hd)

/-- Missing or multiple admissible attractors are independently detectable. -/
def AttractorUniquenessFailure (D : DimensionIndexedModel) (d : Nat)
    (p : ThetaParams) : Prop :=
  ¬ ∃! s : D.State d, IsAdmissibleAttractor D d p s

theorem no_attractor_is_uniqueness_failure (D : DimensionIndexedModel)
    (d : Nat) (p : ThetaParams)
    (h : ¬ ∃ s : D.State d, IsAdmissibleAttractor D d p s) :
    AttractorUniquenessFailure D d p := by
  intro hUnique
  obtain ⟨s, hs, _⟩ := hUnique
  exact h ⟨s, hs⟩

end WCT
