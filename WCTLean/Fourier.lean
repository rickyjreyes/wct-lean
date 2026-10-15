/-
  WCTLean/Fourier.lean

  Minimal Fourier orthogonality scaffolding.
  Full integral orthogonality is left as TODO; we record the statement
  and prove a trivial supporting lemma.
-/

import Mathlib

namespace WCTLean

open Real

/-- Pointwise product-to-sum identity used in Fourier orthogonality proofs:
    `2 cos(a) cos(b) = cos(a - b) + cos(a + b)`. -/
theorem two_cos_mul_cos (a b : ℝ) :
    2 * Real.cos a * Real.cos b = Real.cos (a - b) + Real.cos (a + b) := by
  rw [Real.cos_sub, Real.cos_add]; ring

/--
  TODO: Orthogonality of `cos (n x)` and `cos (m x)` on `[0, 2π]` for `n ≠ m`.

  Statement (left as TODO — proof requires Mathlib's interval integral
  and `Real.cos` integration machinery):

  ```
  ∀ n m : ℤ, n ≠ m →
    ∫ x in (0)..(2*π), Real.cos (n * x) * Real.cos (m * x) = 0
  ```
-/
def cos_orthogonality_TODO : Prop :=
  ∀ n m : ℤ, n ≠ m →
    (∫ x in (0 : ℝ)..(2 * Real.pi), Real.cos (n * x) * Real.cos (m * x)) = 0

/-- The opposite integer frequency is the same real cosine mode. This is
why the original `n ≠ m` integral-orthogonality TODO is not a true theorem
over all integers: one must additionally exclude `n = -m`. -/
theorem cos_opposite_integer_frequency (n : ℤ) (x : ℝ) :
    Real.cos (((-n : ℤ) : ℝ) * x) = Real.cos ((n : ℝ) * x) := by
  simp

/-- Exact normalization of the first nonconstant cosine mode. -/
theorem cos_one_mode_integral_sq :
    (∫ x in (0 : ℝ)..(2 * Real.pi), Real.cos x ^ 2) = Real.pi := by
  rw [Real.integral_cos_sq]
  simp
  ring

/-- The historical integer-frequency orthogonality proposition is false:
n=1 and m=-1 are distinct indices for the same nonzero cosine mode. This
counterexample is distinct from canonical E78's Fisher-information claim. -/
theorem cos_orthogonality_TODO_false : ¬ cos_orthogonality_TODO := by
  intro h
  have hbad := h 1 (-1) (by norm_num)
  have hz : (∫ x in (0 : ℝ)..(2 * Real.pi), Real.cos x ^ 2) = 0 := by
    simpa [pow_two, Real.cos_neg] using hbad
  rw [cos_one_mode_integral_sq] at hz
  exact (ne_of_gt Real.pi_pos) hz

/-- Corrected nondegenerate frequency-separation requirement: distinct
cosine functions require that their integer labels are neither equal nor
opposite. This predicate is only the index condition; the integral theorem
itself is still a separate task. -/
def CosineModesSeparated (n m : ℤ) : Prop := n ≠ m ∧ n ≠ -m

end WCTLean
