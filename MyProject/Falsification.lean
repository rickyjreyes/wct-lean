import MyProject.Theta.Entropy
import MyProject.Theta.Dynamics
import MyProject.Theta.Baselines
import MyProject.LeanTests.DimensionFailure

namespace WCT

/-- The original falsification alternatives, for explicitly supplied model data.
The fixed-point predicate is unchanged; missing fixed points are failures too.
No physical stability is inferred. -/
def LegacyFixedPointContractFalsified (M : ThetaModel) : Prop :=
  (∃ p : ThetaParams, ¬ EntropyMonotoneTheta M p) ∨
  (∃ p : ThetaParams, ∃ s1 s2 : M.State,
    s1 ≠ s2 ∧ IsFixedPoint M p s1 ∧ IsFixedPoint M p s2) ∨
  (∃ p : ThetaParams, ¬ ∃ s : M.State, IsFixedPoint M p s)

/-- A parameter with no fixed point must falsify the fixed-point contract. -/
theorem no_fixedPoint_is_legacy_failure (M : ThetaModel) (p : ThetaParams)
    (h : ¬ ∃ s : M.State, IsFixedPoint M p s) :
    LegacyFixedPointContractFalsified M :=
  Or.inr (Or.inr ⟨p, h⟩)

/-- Adversarial nontrivial model: successor dynamics with constant entropy.
The historical two-disjunct detector missed this model entirely. -/
def FixedPointMissingCountermodel : ThetaModel where
  State := Nat
  state_nonempty := inferInstance
  state_nontrivial := inferInstance
  Theta := fun _ n => n + 1
  Entropy := fun _ => 0
  Energy := fun _ => 0

/-- Executable negative control: the historical detector accepts successor
dynamics even though no fixed point exists. This is not a physical model. -/
theorem fixedPointMissingCountermodel_old_detector_misses :
    ¬ ((∃ p : ThetaParams, ¬ EntropyMonotoneTheta FixedPointMissingCountermodel p) ∨
      (∃ p : ThetaParams, ∃ s1 s2 : FixedPointMissingCountermodel.State,
        s1 ≠ s2 ∧ IsFixedPoint FixedPointMissingCountermodel p s1 ∧
          IsFixedPoint FixedPointMissingCountermodel p s2)) := by
  rintro (⟨p, h⟩ | ⟨p, n, m, hne, hn, hm⟩)
  · apply h
    intro s
    change (0 : ℝ) ≤ 0
    exact le_rfl
  · change Nat.succ n = n at hn
    omega

theorem fixedPointMissingCountermodel_regression :
    LegacyFixedPointContractFalsified FixedPointMissingCountermodel := by
  apply no_fixedPoint_is_legacy_failure FixedPointMissingCountermodel ⟨0⟩
  rintro ⟨n, hn⟩
  change Nat.succ n = n at hn
  omega

/-- The same nonempty successor model has no fixed point, for every parameter. -/
theorem successor_has_no_fixedPoint (p : ThetaParams) :
    ¬ ∃ n : FixedPointMissingCountermodel.State,
      IsFixedPoint FixedPointMissingCountermodel p n := by
  rintro ⟨n, hn⟩
  change Nat.succ n = n at hn
  exact Nat.succ_ne_self n hn

/-- At-most-one is vacuous, but exactly-one must reject this countermodel. -/
theorem successor_uniqueness_regression (p : ThetaParams) :
    AtMostOneFixedPoint FixedPointMissingCountermodel p ∧
      ¬ UniqueFixedPoint FixedPointMissingCountermodel p := by
  constructor
  · intro x y hx hy
    exact (successor_has_no_fixedPoint p ⟨x, hx⟩).elim
  · rintro ⟨x, hx, _⟩
    exact successor_has_no_fixedPoint p ⟨x, hx⟩


/-- Unified model-relative diagnostic. The local state, map and functionals
are projections of D, so unrelated maps cannot be mixed. No physical
realization or validity is certified. The baseline class is compared only
at the designated positive dimension; full physical scope remains OPEN. -/
def FullContractFalsified (D : DimensionIndexedModel) (d : Nat) (hd : 0 < d)
    [AddCommGroup (dimensionSlice D d hd).State]
    [Module ℝ (dimensionSlice D d hd).State]
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
