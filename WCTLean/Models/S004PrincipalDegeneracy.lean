import Mathlib
import WCTLean.Models.CorrectedWeightCalculus

/-!
# S004 corrected curvature weight: exact obstruction to uniform ellipticity

A strictly positive denominator is NOT a uniformly positive coefficient
of the highest spatial derivative. The corrected weight
  F(s) = s / (s + eps² exp(-2 alpha s))²
vanishes at the node s=0 and approaches zero along *strictly positive*
field densities s -> 0.

For every c>0 we construct a concrete s>0 with F(s)<c, using the
already verified field-independent denominator floor. This rules out
a positive uniform principal-coefficient bound on the nonzero field
sector. It does not, by itself, prove ill-posedness of the quasilinear PDE.
-/

namespace WCTLean

/-- The highest-order S004 curvature coefficient is exactly zero at a
field node, despite the positive corrected denominator. -/
theorem correctedRadialWeight_at_node (epsilon alpha : ℝ) :
    correctedRadialWeight epsilon alpha 0 = 0 := by
  simp [correctedRadialWeight]

/-- For every positive regulator, the weight is at most linear in s
with a quantitative denominator determined by epsilon and alpha. -/
theorem correctedRadialWeight_le_linear
    (epsilon alpha s : ℝ)
    (heps : 0 < epsilon) (ha : 0 ≤ alpha) (hs : 0 ≤ s) :
    correctedRadialWeight epsilon alpha s ≤
      s / (complexRegulatorFloor epsilon alpha) ^ 2 := by
  have hm := complexRegulatorFloor_pos epsilon alpha heps
  have hfloor :=
    correctedRadialDenominator_floor epsilon alpha s hs heps ha
  have hD : 0 < correctedRadialDenominator epsilon alpha s :=
    lt_of_lt_of_le hm hfloor
  have hsq :
      (complexRegulatorFloor epsilon alpha) ^ 2 ≤
        (correctedRadialDenominator epsilon alpha s) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hfloor)
      (add_nonneg hm.le hD.le)]
  have hprod := mul_le_mul_of_nonneg_left hsq hs
  unfold correctedRadialWeight
  apply (div_le_div_iff₀
      (sq_pos_of_pos hD) (sq_pos_of_pos hm)).mpr
  nlinarith

/-- Even after excluding all nodes s=0, there is no state-independent
strictly positive lower bound on the highest-order curvature weight. -/
theorem arbitrarily_small_positive_curvature_weight
    (epsilon alpha c : ℝ)
    (heps : 0 < epsilon) (ha : 0 ≤ alpha) (hc : 0 < c) :
    ∃ s : ℝ, 0 < s ∧ correctedRadialWeight epsilon alpha s < c := by
  have hm := complexRegulatorFloor_pos epsilon alpha heps
  let s : ℝ := c * (complexRegulatorFloor epsilon alpha) ^ 2 / 2
  have hs : 0 < s := by
    dsimp [s]
    positivity
  have hbound := correctedRadialWeight_le_linear epsilon alpha s
    heps ha hs.le
  have hdiv : s / (complexRegulatorFloor epsilon alpha) ^ 2 = c / 2 := by
    dsimp [s]
    field_simp [ne_of_gt hm]
  refine ⟨s, hs, ?_⟩
  rw [hdiv] at hbound
  linarith

/-- The uniform-ellipticity assumption fails on all positive densities.
Consequently a standard uniformly parabolic theorem cannot be applied
to the corrected S004 highest-order coefficient without an additional
nonvanishing-amplitude or alternative coercivity hypothesis. -/
theorem no_uniform_positive_curvature_weight
    (epsilon alpha c : ℝ)
    (heps : 0 < epsilon) (ha : 0 ≤ alpha) (hc : 0 < c) :
    ¬ ∀ s : ℝ, 0 < s → c ≤ correctedRadialWeight epsilon alpha s := by
  intro h
  obtain ⟨s, hs, hlt⟩ :=
    arbitrarily_small_positive_curvature_weight epsilon alpha c heps ha hc
  have hge := h s hs
  linarith

end WCTLean
