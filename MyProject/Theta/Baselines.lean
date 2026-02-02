import MyProject.Theta.Definitions

namespace WCT

/-
  Baseline exclusion contract
-/

-- A baseline operator type
axiom BaselineOp : Type

-- Application of a baseline operator
axiom applyBaseline : BaselineOp -> State -> State

/--
  Theta cannot reduce to any baseline operator.
-/
axiom Theta_not_baseline :
  forall (p : ThetaParams) (B : BaselineOp),
    Ne (Theta p) (applyBaseline B)

end WCT
