import MyProject.Theta.Definitions

namespace WCT

def UniqueAttractor (M : ThetaModel) (p : ThetaParams) : Prop :=
  ∀ x y : M.State, IsAttractor M p x → IsAttractor M p y → x = y

/-- Conditional packaging of existence and uniqueness. Neither premise is
asserted here for the physical model. -/
theorem Theta_unique_attractor_of (M : ThetaModel)
    (hex : attractor_exists M) (huniq : attractor_unique M) :
    ∀ p : ThetaParams, ∃ s : M.State, IsAttractor M p s ∧ UniqueAttractor M p := by
  intro p
  obtain ⟨s, hs⟩ := hex p
  exact ⟨s, hs, huniq p⟩

end WCT
