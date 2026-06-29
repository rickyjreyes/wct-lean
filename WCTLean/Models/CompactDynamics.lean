import Mathlib

namespace WCTLean

/-- E36 finite-dimensional averaged update. -/
def averagedUpdate {E : Type*} [AddCommGroup E] [Module ℝ E]
    (mix : ℝ) (average : E → E) (x : E) : E :=
  (1 - mix) • x + mix • average x

/-- E36: a fixed point of the averaging operator remains fixed under every
mixing parameter. -/
theorem averagedUpdate_fixed_of_average_fixed
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (mix : ℝ) (average : E → E) (x : E)
    (hfix : average x = x) :
    averagedUpdate mix average x = x := by
  unfold averagedUpdate
  rw [hfix, ← add_smul]
  have hscalar : (1 - mix) + mix = (1 : ℝ) := by ring
  rw [hscalar]
  exact one_smul ℝ x

/-- M5/E36: a convex averaged update cannot increase the norm when the supplied
local average is norm-nonexpansive at the current state. -/
theorem averagedUpdate_norm_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (mix : ℝ) (average : E → E) (x : E)
    (h0 : 0 ≤ mix) (h1 : mix ≤ 1)
    (havg : ‖average x‖ ≤ ‖x‖) :
    ‖averagedUpdate mix average x‖ ≤ ‖x‖ := by
  unfold averagedUpdate
  calc
    ‖(1 - mix) • x + mix • average x‖
        ≤ ‖(1 - mix) • x‖ + ‖mix • average x‖ := norm_add_le _ _
    _ = |1 - mix| * ‖x‖ + |mix| * ‖average x‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ (1 - mix) * ‖x‖ + mix * ‖x‖ := by
      rw [abs_of_nonneg h0, abs_of_nonneg (sub_nonneg.mpr h1)]
      exact add_le_add_left (mul_le_mul_of_nonneg_left havg h0) _
    _ = ‖x‖ := by ring

/-- M5 explicit norm-bounded state predicate. -/
def InNormBound {E : Type*} [Norm E] (radius : ℝ) (x : E) : Prop :=
  ‖x‖ ≤ radius

/-- M5: the encoded curvature-resource ball is forward invariant under an
averaged update satisfying the displayed local nonexpansiveness assumptions. -/
theorem averagedUpdate_preserves_normBound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (mix radius : ℝ) (average : E → E) (x : E)
    (h0 : 0 ≤ mix) (h1 : mix ≤ 1)
    (havg : ‖average x‖ ≤ ‖x‖)
    (hx : InNormBound radius x) :
    InNormBound radius (averagedUpdate mix average x) := by
  unfold InNormBound at hx ⊢
  exact (averagedUpdate_norm_le mix average x h0 h1 havg).trans hx

/-- M5 contract for a compact finite-band invariant computational sector. -/
structure BandLimitedInvariantSet where
  stateSpace : Type
  boundedOrbit : Prop
  invariant : Prop
  finiteDimensional : Prop

end WCTLean
