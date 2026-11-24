import MyProject.Theta.Definitions

namespace WCT

/-- Existence and uniqueness remain open for the physical model. This is only
the logical equivalence between separately established existence/uniqueness
and unique existence. -/
theorem unique_attractor_of_exists_unique {S : Type} [MetricSpace S]
    (M : ThetaModel S) (p : ThetaParams)
    (he : AttractorExists M p) (hu : AttractorUnique M p) :
    ∃! s : S, IsAttractor (M.step p) s := by
  obtain ⟨s, hs⟩ := he
  exact ⟨s, hs, fun y hy => hu y s hy hs⟩

end WCT
