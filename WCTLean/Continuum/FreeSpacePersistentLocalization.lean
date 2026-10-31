import WCTLean.Continuum.FreeSpaceMassTails

/-!
# Uniform and dynamically persistent free-space localization (#20)

Finite `L²` mass alone gives vanishing tails for each *single* state
(`FreeSpaceMassTails`). This module proves two strictly stronger statements
for the independent whole-plane cubic–quintic model (`β, γ > 0`,
`0 < m ≤ m_B`):

1. **Uniform tightness of the whole minimizer set modulo translations.**
   One radius `R` works simultaneously for *every* constrained minimizer,
   after recentring. This uses the proved Lions-type compactness modulo
   translations and is false for general bounded sets of finite-mass states
   (e.g. dilated profiles spread out).
2. **Dynamical confinement.** Every solution of the whole-plane flow starting
   `δ`-close in `H²` to the minimizer set stays, for **all** real times,
   localized in a ball of the *fixed* radius `R` about some moving center,
   up to mass `η`. Perturbations are arbitrary complex `H²` data: no radial,
   D4-symmetric or mass-preserving restriction.

Neither statement uses a box, a boundary or a confining potential: the
domain is all of `ℝ²` and the radius is produced by the energy
landscape (strict binding / compactness) together with orbital stability.

Scope: independent cubic–quintic Hamiltonian only. This is not the
corrected curvature-dependent energy (where positive-energy constrained
minimization fails, see `CanonicalCurvatureNonattainment`), nor the periodic
D4 root. No pointwise or exponential decay rate is asserted.
-/

open Filter MeasureTheory

namespace WCTLean.Continuum

/-- Mass of a whole-plane `H²` state outside the closed ball of radius `R`
about the origin. -/
noncomputable def massTail (u : PlaneState) (R : ℝ) : ℝ :=
  ∫ x in (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) R)ᶜ, ‖u.val x‖ ^ 2

theorem massTail_nonneg (u : PlaneState) (R : ℝ) : 0 ≤ massTail u R :=
  setIntegral_nonneg (Metric.isClosed_closedBall.measurableSet.compl)
    (fun _ _ => sq_nonneg _)

/-- Tails decrease as the radius grows. -/
theorem massTail_antitone (u : PlaneState) {R R' : ℝ} (h : R ≤ R') :
    massTail u R' ≤ massTail u R := by
  unfold massTail
  refine setIntegral_mono_set
    (ReyesMath.Sobolev.H2.integrable_sq_val u).integrableOn
    (Eventually.of_forall fun _ => sq_nonneg _) ?_
  refine Eventually.of_forall fun x hx => ?_
  change x ∉ Metric.closedBall _ R' at hx
  change x ∉ Metric.closedBall _ R
  exact fun hR => hx (Metric.closedBall_subset_closedBall h hR)

/-- Stability of tails under `L²` perturbation:
`tail(v) ≤ 2 tail(u) + 2 ‖v - u‖²_{L²}`. -/
theorem massTail_perturb (u v : PlaneState) (R : ℝ) :
    massTail v R ≤ 2 * massTail u R + 2 * ‖v.val - u.val‖ ^ 2 := by
  set S := (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) R)ᶜ
  have hS : MeasurableSet S := Metric.isClosed_closedBall.measurableSet.compl
  have hu := ReyesMath.Sobolev.H2.integrable_sq_val u
  have hv := ReyesMath.Sobolev.H2.integrable_sq_val v
  have hw := ReyesMath.Sobolev.integrable_sq_L2 (v.val - u.val)
  have hpt : (fun x => ‖v.val x‖ ^ 2) ≤ᵐ[volume]
      fun x => 2 * ‖u.val x‖ ^ 2 + 2 * ‖(v.val - u.val) x‖ ^ 2 := by
    filter_upwards [Lp.coeFn_sub v.val u.val] with x hx
    rw [hx, Pi.sub_apply]
    have htri : ‖v.val x‖ ≤ ‖u.val x‖ + ‖v.val x - u.val x‖ := by
      calc ‖v.val x‖ = ‖u.val x + (v.val x - u.val x)‖ := by congr 1; abel
        _ ≤ _ := norm_add_le _ _
    have h0 := norm_nonneg (v.val x)
    nlinarith [sq_nonneg (‖u.val x‖ - ‖v.val x - u.val x‖), norm_nonneg (u.val x),
      norm_nonneg (v.val x - u.val x)]
  have hmono : ∫ x in S, ‖v.val x‖ ^ 2 ≤
      ∫ x in S, (2 * ‖u.val x‖ ^ 2 + 2 * ‖(v.val - u.val) x‖ ^ 2) :=
    setIntegral_mono_ae hv.integrableOn
      ((hu.const_mul 2).add (hw.const_mul 2)).integrableOn
      hpt
  rw [integral_add (hu.const_mul 2).integrableOn (hw.const_mul 2).integrableOn,
    integral_const_mul, integral_const_mul] at hmono
  have hwS : ∫ x in S, ‖(v.val - u.val) x‖ ^ 2 ≤ ‖v.val - u.val‖ ^ 2 := by
    rw [ReyesMath.Sobolev.normSq_eq_integral]
    exact setIntegral_le_integral hw (Eventually.of_forall fun _ => sq_nonneg _)
  unfold massTail
  linarith

/-- The `L²` part of the `H²` distance is controlled by the full distance. -/
theorem val_dist_le_distH2 (u v : PlaneState) :
    ‖u.val - v.val‖ ≤ ReyesMath.Sobolev.H2.distH2 u v := by
  unfold ReyesMath.Sobolev.H2.distH2
  have h1 : 0 ≤ ∑ i, ‖u.grad i - v.grad i‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  have h2 := norm_nonneg (u.lap - v.lap)
  linarith

/-- If two states are `H²`-close (distance `< min 1 (η/8)`), the tail of the
first is below `2 tail(second) + η/4`. -/
theorem massTail_of_distH2_lt (u v : PlaneState) (R : ℝ) {η : ℝ}
    (hd : ReyesMath.Sobolev.H2.distH2 v u < min 1 (η / 8)) :
    massTail v R ≤ 2 * massTail u R + η / 4 := by
  have hval := val_dist_le_distH2 v u
  have hd1 : ReyesMath.Sobolev.H2.distH2 v u < 1 := hd.trans_le (min_le_left _ _)
  have hd2 : ReyesMath.Sobolev.H2.distH2 v u < η / 8 := hd.trans_le (min_le_right _ _)
  have hn := norm_nonneg (v.val - u.val)
  have hsq : ‖v.val - u.val‖ ^ 2 ≤ η / 8 := by nlinarith
  have := massTail_perturb u v R
  linarith

/-- **Uniform tightness of the minimizer set modulo translations.** -/
theorem minimizer_set_uniformly_tight
    {β γ k m : ℝ} (hβ : 0 < β) (hγ : 0 < γ)
    (hm : 0 < m) (hmB : m ≤ ReyesMath.StrictBinding.mB β γ k)
    {η : ℝ} (hη : 0 < η) :
    ∃ R : ℝ, ∀ U ∈ ReyesMath.OrbitalStability.Gset β γ k m,
      ∃ y : EuclideanSpace ℝ (Fin 2),
        massTail (ReyesMath.Sobolev.H2.translate y U) R < η := by
  by_contra hcon
  push_neg at hcon
  choose U hU hbad using fun n : ℕ => hcon (n : ℝ)
  have hM : ∀ n, mass (U n) = m := fun n => (hU n).1
  have hE : Tendsto (fun n => energy β γ k (U n)) atTop
      (nhds (constrainedInfimum β γ k m)) := by
    have : (fun n => energy β γ k (U n)) = fun _ => constrainedInfimum β γ k m :=
      funext fun n => (hU n).2
    rw [this]; exact tendsto_const_nhds
  obtain ⟨φ, hφ, y, V, -, -, hconv⟩ :=
    free_space_minimizing_sequences_compact hβ hγ hm hmB U hM hE
  -- The limit profile has a small tail at some integer radius.
  obtain ⟨N0, hN0⟩ := free_space_mass_tail_small V (by positivity : (0 : ℝ) < η / 4)
  have hev : ∀ᶠ n in atTop, ReyesMath.Sobolev.H2.distH2
      (ReyesMath.Sobolev.H2.translate (y n) (U (φ n))) V < min 1 (η / 8) :=
    hconv.eventually (gt_mem_nhds (by positivity))
  obtain ⟨n, hn, hnN⟩ := (hev.and (eventually_ge_atTop N0)).exists
  have hφn : (N0 : ℝ) ≤ (φ n : ℝ) := by
    exact_mod_cast hnN.trans (hφ.id_le n)
  have h1 := massTail_antitone (ReyesMath.Sobolev.H2.translate (y n) (U (φ n))) hφn
  have h2 := massTail_of_distH2_lt V
    (ReyesMath.Sobolev.H2.translate (y n) (U (φ n))) (N0 : ℝ) hn
  have h3 : massTail V (N0 : ℝ) < η / 4 := hN0
  have h4 := hbad (φ n) (y n)
  linarith

/-- **Dynamical free-space confinement.** For every mass threshold `η > 0`
there are `δ > 0` and a radius `R` such that every whole-plane solution
starting within `H²`-distance `δ` of the minimizer set keeps, at **every**
real time, all but mass `η` inside a ball of radius `R` about some center. -/
theorem orbitally_stable_persistent_localization
    {β γ k m : ℝ} (hβ : 0 < β) (hγ : 0 < γ)
    (hm : 0 < m) (hmB : m ≤ ReyesMath.StrictBinding.mB β γ k)
    {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∃ R : ℝ, ∀ u : ℝ → PlaneState,
      ReyesMath.Sobolev.IsSolution β γ k u →
      ReyesMath.OrbitalStability.distX (u 0)
        (ReyesMath.OrbitalStability.Gset β γ k m) < δ →
      ∀ t : ℝ, ∃ y : EuclideanSpace ℝ (Fin 2),
        massTail (ReyesMath.Sobolev.H2.translate y (u t)) R < η := by
  obtain ⟨R, hR⟩ := minimizer_set_uniformly_tight hβ hγ hm hmB
    (by positivity : (0 : ℝ) < η / 4)
  have hε : (0 : ℝ) < min 1 (η / 8) := by positivity
  obtain ⟨δ, hδ, hstab⟩ := independent_orbital_stability hβ hγ hm hmB hε
  have hG : (ReyesMath.OrbitalStability.Gset β γ k m).Nonempty := by
    obtain ⟨u, hu1, hu2⟩ := exists_free_space_minimizer hβ hγ hm hmB
    exact ⟨u, hu1, hu2⟩
  refine ⟨δ, hδ, R, fun u hu h0 t => ?_⟩
  obtain ⟨hbdd, hsup⟩ := hstab u hu h0
  have ht : ReyesMath.OrbitalStability.distX (u t)
      (ReyesMath.OrbitalStability.Gset β γ k m) < min 1 (η / 8) :=
    (le_ciSup hbdd t).trans_lt hsup
  obtain ⟨g, hg, hdist⟩ := ReyesMath.OrbitalStability.exists_of_distX_lt hG ht
  obtain ⟨y, hy⟩ := hR g hg
  refine ⟨y, ?_⟩
  have hdist' : ReyesMath.Sobolev.H2.distH2
      (ReyesMath.Sobolev.H2.translate y (u t))
      (ReyesMath.Sobolev.H2.translate y g) < min 1 (η / 8) := by
    rw [ReyesMath.Sobolev.distH2_translate]; exact hdist
  have := massTail_of_distH2_lt (ReyesMath.Sobolev.H2.translate y g)
    (ReyesMath.Sobolev.H2.translate y (u t)) R hdist'
  linarith

/-- The same dynamical confinement at the exact rational frozen parameters
(`β = γ = frozenBeta`, `k = 1`, `m = frozenMass`) on the whole plane. -/
theorem frozen_persistent_localization {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∃ R : ℝ, ∀ u : ℝ → PlaneState,
      ReyesMath.Sobolev.IsSolution frozenBeta frozenBeta 1 u →
      ReyesMath.OrbitalStability.distX (u 0)
        (ReyesMath.OrbitalStability.Gset frozenBeta frozenBeta 1 frozenMass) < δ →
      ∀ t : ℝ, ∃ y : EuclideanSpace ℝ (Fin 2),
        massTail (ReyesMath.Sobolev.H2.translate y (u t)) R < η :=
  orbitally_stable_persistent_localization frozen_beta_positive
    frozen_beta_positive frozen_mass_positive frozen_below_binding_threshold hη

end WCTLean.Continuum

#print axioms WCTLean.Continuum.massTail_perturb
#print axioms WCTLean.Continuum.minimizer_set_uniformly_tight
#print axioms WCTLean.Continuum.orbitally_stable_persistent_localization
#print axioms WCTLean.Continuum.frozen_persistent_localization
