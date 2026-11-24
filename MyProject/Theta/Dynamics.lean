import MyProject.Theta.Definitions

namespace WCT

def UniqueFixedPoint (M : ThetaModel) (p : ThetaParams) : Prop :=
  ∀ x y : M.State, IsFixedPoint M p x → IsFixedPoint M p y → x = y

/-- Conditional packaging of existence and uniqueness. Neither premise is
asserted here for the physical model. -/
theorem Theta_unique_fixedPoint_of (M : ThetaModel)
    (hex : fixedPoint_exists M) (huniq : fixedPoint_unique M) :
    ∀ p : ThetaParams, ∃ s : M.State, IsFixedPoint M p s ∧ UniqueFixedPoint M p := by
  intro p
  obtain ⟨s, hs⟩ := hex p
  exact ⟨s, hs, huniq p⟩

end WCT
