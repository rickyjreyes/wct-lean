import MyProject.Theta.Core

namespace WCT

/-- Open model property: each parameter admits a non-fixed state. -/
def Theta_nontrivial (M : ThetaModel) : Prop :=
  ∀ p : ThetaParams, ∃ s : M.State, M.Theta p s ≠ s

/-- Congruence follows from function application, without a model assumption. -/
theorem Theta_deterministic (M : ThetaModel) (p : ThetaParams)
    (s1 s2 : M.State) (h : s1 = s2) : M.Theta p s1 = M.Theta p s2 :=
  congrArg (M.Theta p) h

/-- The legacy claim called this "nonlinearity"; its actual formula states
non-injectivity, not nonlinearity. The formula is preserved as an open property. -/
def Theta_noninjective (M : ThetaModel) : Prop :=
  ∀ p : ThetaParams, ∃ s1 s2 : M.State, s1 ≠ s2 ∧ M.Theta p s1 = M.Theta p s2

/-- Open model property: fixed-point existence. -/
def fixedPoint_exists (M : ThetaModel) : Prop :=
  ∀ p : ThetaParams, ∃ s : M.State, IsFixedPoint M p s

/-- Open model property: fixed-point uniqueness. -/
def fixedPoint_unique (M : ThetaModel) : Prop :=
  ∀ (p : ThetaParams) (s1 s2 : M.State),
    IsFixedPoint M p s1 → IsFixedPoint M p s2 → s1 = s2

end WCT
