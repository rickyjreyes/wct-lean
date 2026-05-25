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

end WCTLean
