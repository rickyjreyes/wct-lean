import MyProject.Theta.Definitions

namespace WCT

def EntropyMonotoneTheta (M : ThetaModel) (p : ThetaParams) : Prop :=
  ∀ s : M.State, M.Entropy (M.Theta p s) ≤ M.Entropy s

/-- A flow is supplied as data, not globally postulated. -/
structure FlowModel (M : ThetaModel) where
  Flow : Type
  evalFlow : Flow → M.State → Real → M.State

def EntropyMonotoneFlow (M : ThetaModel) (F : FlowModel M)
    (H : M.State → Real) (Phi : F.Flow) : Prop :=
  ∀ (x : M.State) (t1 t2 : Real), t1 ≤ t2 →
    H (F.evalFlow Phi x t2) ≤ H (F.evalFlow Phi x t1)

end WCT
