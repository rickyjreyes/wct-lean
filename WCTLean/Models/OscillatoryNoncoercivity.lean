import Mathlib

namespace WCTLean

/-!
# Oscillatory curvature witness (algebraic part)

For the corrected WCT complex curvature operator, specialize to a real field,
epsilon = 1 and alpha = 0 on a periodic domain. Consider the smooth modes

  psi_N(x) = sin(N*x_1) / N,    N = n + 1, n : Nat.

At a point where s = sin(N*x_1), the curvature operator reduces exactly to

  theta_N(s) = s^2 / (1 + s^2 / N^2).

The second-derivative amplitude of the same mode is N. The following
declarations show that these curvature values stay in [0, 1] for |s| <= 1,
while N can be arbitrarily large.

This is the algebraic part of a non-coercivity *sequence*, NOT a proof of
time-dependent blowup or a formalization of Sobolev integrals. See
docs/CURVATURE_ENERGY_NONCOERCIVITY.md for the full integral calculation.
-/

/-- The real-valued mode curvature induced by the corrected regularizer
    with epsilon = 1 and alpha = 0. Here r is the positive spatial
    frequency and s is a sine value. -/
noncomputable def oscillatoryModeCurvature (s r : ℝ) : ℝ :=
  s ^ 2 / (1 + s ^ 2 / r ^ 2)

/-- Despite high spatial frequency, each mode's regularized curvature
    magnitude is at most one. -/
theorem oscillatoryModeCurvature_bounds
    (s r : ℝ) (hlo : -1 ≤ s) (hhi : s ≤ 1) (hr : 0 < r) :
    0 ≤ oscillatoryModeCurvature s r ∧
      oscillatoryModeCurvature s r ≤ 1 := by
  have hs2 : 0 ≤ s ^ 2 := sq_nonneg s
  have hproduct : 0 ≤ (1 + s) * (1 - s) :=
    mul_nonneg (by linarith) (by linarith)
  have hs2le : s ^ 2 ≤ 1 := by
    nlinarith
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  have hratio : 0 ≤ s ^ 2 / r ^ 2 :=
    div_nonneg hs2 hr2.le
  have hden : 0 < 1 + s ^ 2 / r ^ 2 := by
    linarith
  unfold oscillatoryModeCurvature
  constructor
  · exact div_nonneg hs2 hden.le
  · apply (div_le_iff₀ hden).2
    calc
      s ^ 2 ≤ s ^ 2 * (1 + s ^ 2 / r ^ 2) := by
        have hnonneg := mul_nonneg hs2 hratio
        nlinarith
      _ ≤ 1 * (1 + s ^ 2 / r ^ 2) :=
        mul_le_mul_of_nonneg_right hs2le hden.le

/-- Arbitrarily high second-derivative amplitudes coexist with the same
    uniform pointwise curvature bound, in the algebraic mode family. -/
theorem oscillatoryMode_unbounded_second_derivative (C : ℝ) :
    ∃ n : ℕ, C < (n : ℝ) + 1 ∧
      ∀ s : ℝ, -1 ≤ s → s ≤ 1 →
        0 ≤ oscillatoryModeCurvature s ((n : ℝ) + 1) ∧
        oscillatoryModeCurvature s ((n : ℝ) + 1) ≤ 1 := by
  obtain ⟨n, hn⟩ := exists_nat_gt C
  refine ⟨n, by linarith, ?_⟩
  intro s hlo hhi
  apply oscillatoryModeCurvature_bounds s ((n : ℝ) + 1) hlo hhi
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  linarith

end WCTLean
