import MyProject.Theta.Definitions

namespace WCT

structure BaselineModel (M : ThetaModel) where
  BaselineOp : Type
  baseline_nonempty : Nonempty BaselineOp
  applyBaseline : BaselineOp → M.State → M.State

/-- Open exclusion property of a supplied baseline class. -/
def Theta_not_baseline (M : ThetaModel) (B : BaselineModel M) : Prop :=
  ∀ (p : ThetaParams) (b : B.BaselineOp),
    ∃ x : M.State, M.Theta p x ≠ B.applyBaseline b x

/-- A supplied distinguishing witness proves operator inequality. -/
theorem theta_ne_baseline_of_witness (M : ThetaModel) (B : BaselineModel M)
    (p : ThetaParams) (b : B.BaselineOp) (x : M.State)
    (hx : M.Theta p x ≠ B.applyBaseline b x) :
    M.Theta p ≠ B.applyBaseline b := by
  intro h
  exact hx (congrFun h x)


/-- Explicit comparison with every real-linear map. No arbitrary choice of
baseline class can discharge this obligation. -/
def ExcludesLinearBaselines (M : ThetaModel) [AddCommGroup M.State]
    [Module ℝ M.State] : Prop :=
  ∀ p : ThetaParams, ∀ L : M.State →ₗ[ℝ] M.State,
    ∃ x : M.State, M.Theta p x ≠ L x

end WCT
