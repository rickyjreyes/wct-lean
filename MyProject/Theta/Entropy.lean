import MyProject.Theta.Definitions

namespace WCT

def EntropyMonotoneTheta (M : ThetaModel) (p : ThetaParams) : Prop :=
  ∀ s : M.State, M.Entropy (M.Theta p s) ≤ M.Entropy s

/-- A flow is supplied as data, not globally postulated. -/
structure FlowModel (M : ThetaModel) where
  Flow : Type
  flow_nonempty : Nonempty Flow
  evalFlow : Flow → M.State → Real → M.State

def EntropyMonotoneFlow (M : ThetaModel) (F : FlowModel M)
    (H : M.State → Real) (Phi : F.Flow) : Prop :=
  ∀ (x : M.State) (t1 t2 : Real), t1 ≤ t2 →
    H (F.evalFlow Phi x t2) ≤ H (F.evalFlow Phi x t1)


/-- The flow laws are OPEN properties of independently supplied trajectories. -/
def FlowLaws (M : ThetaModel) (F : FlowModel M) : Prop :=
  (∀ Φ x, F.evalFlow Φ x 0 = x) ∧
  (∀ Φ x (t u : ℝ), 0 ≤ t → 0 ≤ u →
    F.evalFlow Φ x (t + u) = F.evalFlow Φ (F.evalFlow Φ x u) t)

def StrictEntropyDissipation (M : ThetaModel) : Prop :=
  ∀ p s, ¬ IsFixedPoint M p s →
    M.Entropy (M.Theta p s) < M.Entropy s

end WCT
