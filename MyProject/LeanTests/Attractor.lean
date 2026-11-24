import MyProject.Theta.Dynamics

namespace WCT

/-- LEAN-2: the unique-existence formulation follows from the two explicitly
displayed obligations; no global uniqueness or existence is assumed. -/
theorem Theta_unique_fixedPoint_existsUnique_of (M : ThetaModel)
    (hex : fixedPoint_exists M) (huniq : fixedPoint_unique M) :
    ∀ p : ThetaParams, ∃! s : M.State, IsFixedPoint M p s := by
  intro p
  obtain ⟨s, hs⟩ := hex p
  exact ⟨s, hs, fun y hy => huniq p y s hy hs⟩

end WCT
