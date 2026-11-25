import MyProject.Theta.Definitions

namespace WCT

/-- Totality is immediate for the supplied total function; this does not
establish that a physical evolution defines such a function. -/
theorem Theta_total (M : ThetaModel) (p : ThetaParams) (x : M.State) :
    ∃ y : M.State, M.Theta p x = y :=
  ⟨M.Theta p x, rfl⟩

end WCT
