import WCTLean.Continuum.CubicQuinticWholeSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Spatial L²-tail localization of genuine whole-space H² fields

Every H²(R²; C) state has integrable mass density, and mass outside
expanding Euclidean balls tends to zero. This theorem applies to the
proved constrained cubic-quintic minimizers. It does not assert a
pointwise or exponential decay rate and by itself does not distinguish
energetic confinement from generic finite-mass states.
-/

open Filter MeasureTheory

namespace WCTLean.Continuum

private abbrev Space2 := EuclideanSpace ℝ (Fin 2)

/-- The L² mass outside expanding closed Euclidean balls tends to zero
for each weak-Sobolev H² state. This is a continuum integral, not a
finite-grid or bounded-box surrogate. -/
theorem free_space_mass_tail_tendsto_zero (u : PlaneState) :
    Tendsto
      (fun n : ℕ =>
        ∫ x in (Metric.closedBall (0 : Space2) (n : ℝ))ᶜ,
          ‖u.val x‖ ^ 2)
      atTop (nhds (0 : ℝ)) := by
  let S : ℕ → Set Space2 := fun n =>
    (Metric.closedBall (0 : Space2) (n : ℝ))ᶜ
  have hsm : ∀ n : ℕ, MeasurableSet (S n) := by
    intro n
    exact isClosed_closedBall.measurableSet.compl
  have hanti : Antitone S := by
    intro i j hij x hx
    change x ∉ Metric.closedBall (0 : Space2) (j : ℝ) at hx
    change x ∉ Metric.closedBall (0 : Space2) (i : ℝ)
    intro hxi
    have hle : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
    have hxj : x ∈ Metric.closedBall (0 : Space2) (j : ℝ) :=
      Metric.mem_closedBall.mpr ((Metric.mem_closedBall.mp hxi).trans hle)
    exact hx hxj
  have h_empty : (⋂ n : ℕ, S n) = ∅ := by
    ext x
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_gt ‖x‖
      have hnot : x ∉ Metric.closedBall (0 : Space2) (n : ℝ) :=
        Set.mem_iInter.mp hx n
      have hmem : x ∈ Metric.closedBall (0 : Space2) (n : ℝ) := by
        change dist x (0 : Space2) ≤ (n : ℝ)
        simpa [dist_zero_right] using (le_of_lt hn)
      exact hnot hmem
    · intro hx
      exact hx.elim
  have hi : Integrable (fun x : Space2 => ‖u.val x‖ ^ 2) :=
    ReyesMath.Sobolev.H2.integrable_sq_val u
  have hlim := tendsto_setIntegral_of_antitone
    (f := fun x : Space2 => ‖u.val x‖ ^ 2)
    (μ := volume) (s := S)
    hsm hanti ⟨0, hi.integrableOn⟩
  simpa [S, h_empty] using hlim

/-- For every positive threshold one can select a finite radius outside
which the total L² mass is smaller than that threshold. -/
theorem free_space_mass_tail_small (u : PlaneState)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ,
      (∫ x in (Metric.closedBall (0 : Space2) (n : ℝ))ᶜ,
        ‖u.val x‖ ^ 2) < ε := by
  have h := free_space_mass_tail_tendsto_zero u
  have he : ∀ᶠ n : ℕ in atTop,
      (∫ x in (Metric.closedBall (0 : Space2) (n : ℝ))ᶜ,
        ‖u.val x‖ ^ 2) < ε :=
    h.eventually (Iio_mem_nhds hε)
  exact he.exists

/-- The actual energy-attaining whole-plane minimizer has vanishing
spatial mass tails. No radial assumption or box boundary is imposed. -/
theorem exists_free_space_minimizer_with_mass_tails
    {β γ k m : ℝ} (hβ : 0 < β) (hγ : 0 < γ)
    (hm : 0 < m) (hmB : m ≤ ReyesMath.StrictBinding.mB β γ k) :
    ∃ u : PlaneState,
      mass u = m ∧ energy β γ k u = constrainedInfimum β γ k m ∧
      Tendsto
        (fun n : ℕ =>
          ∫ x in (Metric.closedBall (0 : Space2) (n : ℝ))ᶜ,
            ‖u.val x‖ ^ 2)
        atTop (nhds (0 : ℝ)) := by
  obtain ⟨u, huM, huE⟩ :=
    exists_free_space_minimizer hβ hγ hm hmB
  exact ⟨u, huM, huE, free_space_mass_tail_tendsto_zero u⟩

#print axioms WCTLean.Continuum.free_space_mass_tail_tendsto_zero
#print axioms WCTLean.Continuum.free_space_mass_tail_small
#print axioms WCTLean.Continuum.exists_free_space_minimizer_with_mass_tails

end WCTLean.Continuum
