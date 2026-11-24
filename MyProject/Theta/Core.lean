import Mathlib

namespace WCT

structure ThetaParams where
  id : Nat

/-- Explicit abstract model data. No globally postulated type or operator.
A concrete physical realization must supply these fields independently. -/
structure ThetaModel where
  State : Type
  Theta : ThetaParams → State → State
  Entropy : State → Real
  Energy : State → Real

/-- Historical fixed-point predicate. Fixed points alone do not establish
dynamical attraction or orbital stability. -/
def IsFixedPoint (M : ThetaModel) (p : ThetaParams) (s : M.State) : Prop :=
  M.Theta p s = s

/-- Local dynamical attraction for the discrete iteration of a supplied Theta
map. This is an open property, not a consequence of being a fixed point.
It makes no claim of Lyapunov or orbital stability or of PDE attraction. -/
def IsAttractingFixedPoint (M : ThetaModel) [MetricSpace M.State]
    (p : ThetaParams) (s : M.State) : Prop :=
  IsFixedPoint M p s ∧
    ∃ r : ℝ, 0 < r ∧ ∀ x : M.State, dist x s < r →
      Filter.Tendsto (fun k : ℕ => Function.iterate (M.Theta p) k x)
        Filter.atTop (nhds s)

end WCT
