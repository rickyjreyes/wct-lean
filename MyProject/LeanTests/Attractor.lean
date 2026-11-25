import MyProject.Theta.Dynamics

namespace WCT

/-- LEAN-2: the actual unique fixed-point existence obligation. No proof is
claimed until an independently verified concrete Theta model is supplied. -/
def Theta_unique_fixedPoint_existsUnique (M : ThetaModel) : Prop :=
  ∀ p : ThetaParams, ∃! s : M.State, IsFixedPoint M p s

end WCT
