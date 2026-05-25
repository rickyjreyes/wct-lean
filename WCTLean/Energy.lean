/-
  WCTLean/Energy.lean

  Basic nonnegativity lemmas and a toy WCT energy skeleton.
-/

import Mathlib

namespace WCTLean

variable {x y a b : ℝ}

/-- Any real square is nonnegative. -/
theorem square_nonnegative (x : ℝ) : 0 ≤ x ^ 2 := by
  exact sq_nonneg x

/-- The "norm-square" form `x * x` is nonnegative. -/
theorem norm_sq_nonnegative (x : ℝ) : 0 ≤ x * x :=
  mul_self_nonneg x

/-- A nonnegative coefficient times a square is nonnegative. -/
theorem positive_coeff_square_nonnegative
    (h : 0 ≤ a) (x : ℝ) : 0 ≤ a * x ^ 2 :=
  mul_nonneg h (sq_nonneg x)

/-- Sum of two nonnegatives is nonnegative. -/
theorem sum_two_nonnegative
    (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ x + y :=
  add_nonneg hx hy

/-- Toy WCT energy skeleton: `E(x,y) = a x² + b y²`. -/
def toyEnergy (a b x y : ℝ) : ℝ := a * x ^ 2 + b * y ^ 2

/-- The toy quadratic energy is nonnegative when both coefficients are. -/
theorem positive_quadratic_energy_nonnegative
    (ha : 0 ≤ a) (hb : 0 ≤ b) (x y : ℝ) :
    0 ≤ toyEnergy a b x y := by
  show 0 ≤ a * x ^ 2 + b * y ^ 2
  exact add_nonneg
    (positive_coeff_square_nonnegative ha x)
    (positive_coeff_square_nonnegative hb y)

end WCTLean
