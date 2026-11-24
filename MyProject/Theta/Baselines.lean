import MyProject.Theta.Definitions

namespace WCT

/-
  Baseline exclusion contract
-/

-- A baseline operator type
axiom BaselineOp : Type

-- Application of a baseline operator
axiom applyBaseline : BaselineOp -> State -> State

-- Theta_not_baseline: removed assumed conclusion; no proof is claimed.

end WCT
