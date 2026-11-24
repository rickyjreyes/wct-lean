import MyProject.Theta.Definitions

namespace WCT

/-- Open inequality for a specified model; no monotonicity is postulated. -/
def EntropyMonotoneTheta {S : Type} (M : ThetaModel S) (p : ThetaParams) : Prop :=
  ∀ s : S, M.entropy (M.step p s) ≤ M.entropy s

/-- Open inequality along an explicitly supplied flow evaluation. -/
def EntropyMonotoneFlow {S : Type} (H : S → ℝ) (Phi : S → ℝ → S) : Prop :=
  ∀ (x : S) (t1 t2 : ℝ), t1 ≤ t2 → H (Phi x t2) ≤ H (Phi x t1)

end WCT
