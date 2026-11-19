import Mathlib

namespace WCTLean

/-! E15 and E31: explicit differential/discrete hypotheses and their
consequences. These declarations do not derive the nonlinear modal projection
estimate or entropy production from WCT dynamics. -/

/-- E15, with P = |Ahat_k|²: the quartic amplitude term is P². -/
def modalGrowthRhs (growth damping power : ℝ) : ℝ :=
  2 * growth * power - damping * power ^ 2

/-- E15's actual differentiable-time inequality, conditional on the
model-specific projection estimate at every time. -/
def ModalGrowthBound (power : ℝ → ℝ) (growth damping : ℝ) : Prop :=
  0 < damping ∧ ∀ t, 0 ≤ power t ∧
    HasDerivAt power (deriv power t) t ∧
    deriv power t ≤ modalGrowthRhs growth damping (power t)

/-- E15: a nonnegative mode above the supplied saturation threshold cannot
have positive instantaneous power growth. This is not a global PDE bound. -/
theorem modalGrowth_nonpositive_above_threshold
    (power : ℝ → ℝ) (growth damping t : ℝ)
    (h : ModalGrowthBound power growth damping)
    (hThreshold : 2 * growth ≤ damping * power t) :
    deriv power t ≤ 0 := by
  have hp := (h.2 t).1
  have hb := (h.2 t).2.2
  have hm := mul_le_mul_of_nonneg_right hThreshold hp
  unfold modalGrowthRhs at hb
  nlinarith

/-- E31: entropy drop at a discrete step, with the canonical sign. -/
def spectralEntropyDrop (entropy : ℕ → ℝ) (n : ℕ) : ℝ :=
  entropy n - entropy (n + 1)

/-- E31 explicitly requires a nonnegative, independently supplied
dissipation and its model-specific lower bound; it does not define
dissipation circularly from entropy drop. -/
def EntropyDissipationBound (entropy dissipation : ℕ → ℝ) (c : ℝ) : Prop :=
  0 ≤ c ∧ ∀ n, 0 ≤ dissipation n ∧
    c * dissipation n ≤ spectralEntropyDrop entropy n

theorem entropy_nonincreasing_of_dissipation_bound
    (entropy dissipation : ℕ → ℝ) (c : ℝ)
    (h : EntropyDissipationBound entropy dissipation c) (n : ℕ) :
    entropy (n + 1) ≤ entropy n := by
  have hprod := mul_nonneg h.1 (h.2 n).1
  have hdrop := (h.2 n).2
  unfold spectralEntropyDrop at hdrop
  linarith

/-- E31: telescoping bound on the entire finite dissipation budget. -/
theorem cumulative_dissipation_le_entropy_drop
    (entropy dissipation : ℕ → ℝ) (c : ℝ)
    (h : EntropyDissipationBound entropy dissipation c) (N : ℕ) :
    c * (∑ n ∈ Finset.range N, dissipation n) ≤ entropy 0 - entropy N := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hstep := (h.2 N).2
    unfold spectralEntropyDrop at hstep
    rw [Finset.sum_range_succ, mul_add]
    linarith

end WCTLean
