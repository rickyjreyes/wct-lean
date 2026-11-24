import MyProject.Theta.Dynamics

namespace WCT

/-- LEAN-2: the unique-existence formulation follows from the two explicitly
displayed obligations; no global uniqueness or existence is assumed. -/
theorem Theta_unique_attractor_existsUnique_of (M : ThetaModel)
    (hex : attractor_exists M) (huniq : attractor_unique M) :
    ∀ p : ThetaParams, ∃! s : M.State, IsAttractor M p s := by
  intro p
  obtain ⟨s, hs⟩ := hex p
  exact ⟨s, hs, fun y hy => huniq p y s hy hs⟩

end WCT
