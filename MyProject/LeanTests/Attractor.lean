import MyProject.Theta.Dynamics

namespace WCT

/-- Unproved universal unique-attraction obligation for the specified model. -/
def UniqueAttractorObligation {S : Type} [MetricSpace S] (M : ThetaModel S) : Prop :=
  ∀ p : ThetaParams, ∃! s : S, IsAttractor (M.step p) s

end WCT
