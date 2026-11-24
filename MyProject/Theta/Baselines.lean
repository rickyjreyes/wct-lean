import MyProject.Theta.Definitions

namespace WCT

/-- Open exclusion obligation for a specified class of baseline operators.
A distinguishing state must exist for each baseline. -/
def BaselineExclusion {S : Type} (M : ThetaModel S) (p : ThetaParams)
    (baselines : Set (S → S)) : Prop :=
  ∀ B ∈ baselines, ∃ s : S, M.step p s ≠ B s

theorem baseline_ne_of_witness {S : Type} (M : ThetaModel S)
    (p : ThetaParams) (B : S → S) (s : S) (h : M.step p s ≠ B s) :
    M.step p ≠ B := by
  intro he
  exact h (congrFun he s)

end WCT
