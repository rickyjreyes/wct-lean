import MyProject.Theta.Definitions

namespace WCT

/-- Dimension-indexed explicit model. The index alone does not certify that the
state spaces realize a physical PDE in those dimensions. -/
structure DimensionModel where
  StateAt : ℕ → Type
  metric : ∀ n, MetricSpace (StateAt n)
  model : ∀ n, ThetaModel (StateAt n)

def HasDimensionalAttractor (D : DimensionModel) (n : ℕ) (p : ThetaParams) : Prop :=
  @AttractorExists (D.StateAt n) (D.metric n) (D.model n) p

/-- Open existence obligation, restricted to positive dimensions 1 through 3. -/
def LowDimensionObligation (D : DimensionModel) : Prop :=
  ∀ n : ℕ, 0 < n → n ≤ 3 → ∀ p : ThetaParams, HasDimensionalAttractor D n p

/-- Open exclusion obligation for every dimension greater than three. -/
def HighDimensionObligation (D : DimensionModel) : Prop :=
  ∀ n : ℕ, 3 < n → ∀ p : ThetaParams, ¬ HasDimensionalAttractor D n p

end WCT
