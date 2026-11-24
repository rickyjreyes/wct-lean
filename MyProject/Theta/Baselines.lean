import MyProject.Theta.Definitions

namespace WCT

structure BaselineModel (M : ThetaModel) where
  BaselineOp : Type
  applyBaseline : BaselineOp → M.State → M.State

/-- Open exclusion property of a supplied baseline class. -/
def Theta_not_baseline (M : ThetaModel) (B : BaselineModel M) : Prop :=
  ∀ (p : ThetaParams) (b : B.BaselineOp), M.Theta p ≠ B.applyBaseline b

end WCT
