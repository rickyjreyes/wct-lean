/-
  WCTLean/Koide.lean

  Formal skeleton for the Koide expression.
  We prove only domain safety: the denominator is positive when masses are.
-/

import Mathlib

namespace WCTLean

open Real

/-- The Koide expression
    `K(me, mμ, mτ) = (me + mμ + mτ) / (√me + √mμ + √mτ)²`. -/
noncomputable def koide (me mmu mtau : ℝ) : ℝ :=
  (me + mmu + mtau) / (Real.sqrt me + Real.sqrt mmu + Real.sqrt mtau) ^ 2

/-- The square-root sum is positive when at least one mass is positive
    (we use all three positive for simplicity). -/
theorem koide_sqrt_sum_pos
    {me mmu mtau : ℝ}
    (he : 0 < me) (hmu : 0 < mmu) (htau : 0 < mtau) :
    0 < Real.sqrt me + Real.sqrt mmu + Real.sqrt mtau := by
  have h1 : 0 < Real.sqrt me := Real.sqrt_pos.mpr he
  have h2 : 0 < Real.sqrt mmu := Real.sqrt_pos.mpr hmu
  have h3 : 0 < Real.sqrt mtau := Real.sqrt_pos.mpr htau
  linarith

/-- The Koide denominator `(√me + √mμ + √mτ)²` is positive for positive masses. -/
theorem koide_denominator_positive
    {me mmu mtau : ℝ}
    (he : 0 < me) (hmu : 0 < mmu) (htau : 0 < mtau) :
    0 < (Real.sqrt me + Real.sqrt mmu + Real.sqrt mtau) ^ 2 := by
  have hsum := koide_sqrt_sum_pos he hmu htau
  exact pow_pos hsum 2

/-- The Koide numerator is positive for positive masses. -/
theorem koide_numerator_positive
    {me mmu mtau : ℝ}
    (he : 0 < me) (hmu : 0 < mmu) (htau : 0 < mtau) :
    0 < me + mmu + mtau := by
  linarith

/-- The Koide expression is well-defined (denominator nonzero) for positive masses. -/
theorem koide_well_defined
    {me mmu mtau : ℝ}
    (he : 0 < me) (hmu : 0 < mmu) (htau : 0 < mtau) :
    (Real.sqrt me + Real.sqrt mmu + Real.sqrt mtau) ^ 2 ≠ 0 :=
  ne_of_gt (koide_denominator_positive he hmu htau)

/-- The Koide expression is positive for positive masses. -/
theorem koide_positive
    {me mmu mtau : ℝ}
    (he : 0 < me) (hmu : 0 < mmu) (htau : 0 < mtau) :
    0 < koide me mmu mtau := by
  unfold koide
  exact div_pos
    (koide_numerator_positive he hmu htau)
    (koide_denominator_positive he hmu htau)

end WCTLean
