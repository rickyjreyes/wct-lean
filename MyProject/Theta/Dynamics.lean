import MyProject.Theta.Definitions

namespace WCT

def UniqueFixedPoint (M : ThetaModel) (p : ThetaParams) : Prop :=
  ∀ x y : M.State, IsFixedPoint M p x → IsFixedPoint M p y → x = y

/-- Independent existence and uniqueness of actual attracting fixed points
is an open mathematical obligation, not a projection counted as a proof. -/
def Theta_unique_attractor (M : ThetaModel) [MetricSpace M.State] : Prop :=
  ∀ p : ThetaParams, ∃! s : M.State, IsAttractingFixedPoint M p s

end WCT
