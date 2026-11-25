import MyProject.Theta.Definitions

namespace WCT

/-- Uniqueness conditional on existence; may hold when no fixed point exists. -/
def AtMostOneFixedPoint (M : ThetaModel) (p : ThetaParams) : Prop :=
  ∀ x y : M.State, IsFixedPoint M p x → IsFixedPoint M p y → x = y

/-- Exactly one fixed point, including existence. Not a stability claim. -/
def UniqueFixedPoint (M : ThetaModel) (p : ThetaParams) : Prop :=
  ∃! x : M.State, IsFixedPoint M p x

theorem uniqueFixedPoint_iff_exists_and_atMostOne (M : ThetaModel) (p : ThetaParams) :
    UniqueFixedPoint M p ↔
      (∃ x : M.State, IsFixedPoint M p x) ∧ AtMostOneFixedPoint M p := by
  constructor
  · rintro ⟨x, hx, hu⟩
    exact ⟨⟨x, hx⟩, fun y z hy hz => (hu y hy).trans (hu z hz).symm⟩
  · rintro ⟨⟨x, hx⟩, hu⟩
    exact ⟨x, hx, fun y hy => hu y x hy hx⟩

/-- Independent existence and uniqueness of actual attracting fixed points
is an open mathematical obligation, not a projection counted as a proof. -/
def Theta_unique_attractor (M : ThetaModel) [MetricSpace M.State] : Prop :=
  ∀ p : ThetaParams, ∃! s : M.State, IsAttractingFixedPoint M p s

/-- Unique asymptotically stable fixed points are a separate OPEN property.
This is not a physical or orbital stability certificate. -/
def Theta_unique_asymptoticallyStable (M : ThetaModel) [MetricSpace M.State] : Prop :=
  ∀ p : ThetaParams, ∃! s : M.State, IsAsymptoticallyStable M p s

/-- Combining independently established existence and at-most-one attracting
fixed point yields exact unique existence, without asserting either premise. -/
theorem unique_attractor_of_exists_and_atMostOne
    (M : ThetaModel) [MetricSpace M.State] (p : ThetaParams)
    (he : ∃ s : M.State, IsAttractingFixedPoint M p s)
    (hu : ∀ x y : M.State, IsAttractingFixedPoint M p x →
      IsAttractingFixedPoint M p y → x = y) :
    ∃! s : M.State, IsAttractingFixedPoint M p s := by
  obtain ⟨s, hs⟩ := he
  exact ⟨s, hs, fun y hy => hu y s hy hs⟩

end WCT
