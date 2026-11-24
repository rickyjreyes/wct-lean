import MyProject.Theta.Definitions

namespace WCT

/-- Function totality only; this does not prove PDE well-posedness. -/
theorem Theta_total {S : Type} (M : ThetaModel S) (p : ThetaParams) (x : S) :
    ∃ y : S, M.step p x = y :=
  ⟨M.step p x, rfl⟩

end WCT
