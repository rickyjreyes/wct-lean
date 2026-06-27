import Mathlib

namespace WCTLean

def averagedUpdate {E : Type*} [AddCommGroup E] [Module ℝ E]
    (mix : ℝ) (average : E → E) (x : E) : E :=
  (1 - mix) • x + mix • average x

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

structure BandLimitedInvariantSet where
  stateSpace : Type
  boundedOrbit : Prop
  invariant : Prop
  finiteDimensional : Prop

end WCTLean
