import Mathlib

namespace WCT

structure ThetaParams where
  id : Nat

/-- Explicit model data, not global axioms or a claim of physical realization. -/
structure ThetaModel (S : Type) where
  step : ThetaParams → S → S
  entropy : S → ℝ
  energy : S → ℝ

def IsFixedPoint {S : Type} (f : S → S) (s : S) : Prop :=
  f s = s

/-- A locally asymptotically stable fixed point of a discrete metric-space map.
Both Lyapunov stability and convergence from a neighborhood are required. -/
def IsAttractor {S : Type} [MetricSpace S] (f : S → S) (s : S) : Prop :=
  IsFixedPoint f s ∧
  (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ x : S, dist x s < δ → ∀ n : ℕ, dist (Function.iterate f n x) s < ε) ∧
  (∃ δ : ℝ, 0 < δ ∧ ∀ x : S, dist x s < δ →
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      dist (Function.iterate f n x) s < ε)

end WCT
