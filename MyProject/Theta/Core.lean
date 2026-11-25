import Mathlib

namespace WCT

structure ThetaParams where
  id : Nat

/-- Explicit abstract model data. No globally postulated type or operator.
A concrete physical realization must supply these fields independently. -/
structure ThetaModel where
  State : Type
  state_nonempty : Nonempty State
  state_nontrivial : Nontrivial State
  Theta : ThetaParams → State → State
  Entropy : State → Real
  Energy : State → Real

/-- Historical fixed-point predicate. Fixed points alone do not establish
dynamical attraction or orbital stability. -/
def IsFixedPoint (M : ThetaModel) (p : ThetaParams) (s : M.State) : Prop :=
  M.Theta p s = s

/-- Iteration of the supplied map, starting from the initial state. -/
def thetaIterate (M : ThetaModel) (p : ThetaParams) : Nat → M.State → M.State
  | 0, x => x
  | k + 1, x => M.Theta p (thetaIterate M p k x)

/-- Local dynamical attraction for the discrete iteration of a supplied Theta
map. This is an open property, not a consequence of being a fixed point.
It makes no claim of Lyapunov or orbital stability or of PDE attraction. -/
def IsAttractingFixedPoint (M : ThetaModel) [MetricSpace M.State]
    (p : ThetaParams) (s : M.State) : Prop :=
  IsFixedPoint M p s ∧
    ∃ r : ℝ, 0 < r ∧ ∀ x : M.State, dist x s < r →
      Filter.Tendsto (fun k : ℕ => thetaIterate M p k x)
        Filter.atTop (nhds s)


/-- Lyapunov stability is independent of eventual convergence. -/
def IsLyapunovStable (M : ThetaModel) [MetricSpace M.State]
    (p : ThetaParams) (s : M.State) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ x : M.State, dist x s < δ → ∀ k : ℕ,
      dist (thetaIterate M p k x) s < ε

def HasNearbyPerturbations {X : Type} [MetricSpace X]
    (A : X → Prop) (s : X) : Prop :=
  ∀ r : ℝ, 0 < r → ∃ x : X, A x ∧ x ≠ s ∧ dist x s < r

/-- Pointwise asymptotic stability; not orbital stability of a PDE. -/
def IsAsymptoticallyStable (M : ThetaModel) [MetricSpace M.State]
    (p : ThetaParams) (s : M.State) : Prop :=
  IsAttractingFixedPoint M p s ∧ IsLyapunovStable M p s ∧
    HasNearbyPerturbations (fun _ : M.State => True) s

/-- Open realization obligations, not properties of arbitrary supplied data. -/
def EnergyBoundedBelow (M : ThetaModel) : Prop :=
  ∃ C : ℝ, ∀ s : M.State, C ≤ M.Energy s

def EnergyConserved (M : ThetaModel) : Prop :=
  ∀ p s, M.Energy (M.Theta p s) = M.Energy s

end WCT
