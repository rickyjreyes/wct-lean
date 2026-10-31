import MathProofs.WholeSpaceMinimizers
import MathProofs.OrbitalStability
import MathProofs.StrictBinding

/-!
# Independent whole-space cubic–quintic continuum results

This is the independent fourth-order cubic–quintic Hamiltonian on
H²(ℝ²; ℂ). It is not the corrected curvature-dependent WCT action, nor the
periodic numerical D4 stationary root. All Sobolev definitions and results
are imported from the SHA-pinned `reyes_math` Lake dependency.
-/

open Filter

namespace WCTLean.Continuum

abbrev PlaneState := ReyesMath.Sobolev.H2 2

noncomputable abbrev mass (u : PlaneState) : ℝ :=
  ReyesMath.Sobolev.H2.M u

noncomputable abbrev energy (β γ k : ℝ) (u : PlaneState) : ℝ :=
  ReyesMath.Sobolev.H2.energy β γ k u

noncomputable abbrev constrainedInfimum (β γ k m : ℝ) : ℝ :=
  ReyesMath.Sobolev.H2.Imin β γ k m

/-- The WCT-Lean names are definitionally equal to the genuine weak-Sobolev
mass and Hamiltonian, not an invented surrogate. -/
theorem model_correspondence (β γ k : ℝ) (u : PlaneState) :
    mass u = ReyesMath.Sobolev.H2.M u ∧
    energy β γ k u = ReyesMath.Sobolev.H2.energy β γ k u := by
  exact ⟨rfl, rfl⟩

/-- Whole-space existence, mass constraint and energy attainment. -/
theorem exists_free_space_minimizer
    {β γ k m : ℝ} (hβ : 0 < β) (hγ : 0 < γ)
    (hm : 0 < m) (hmB : m ≤ ReyesMath.StrictBinding.mB β γ k) :
    ∃ u : PlaneState, mass u = m ∧
      energy β γ k u = constrainedInfimum β γ k m := by
  exact ReyesMath.WholeSpace.exists_minimizer hβ hγ hm hmB

/-- A positive-mass free-space minimizer is genuinely nonzero in L². -/
theorem exists_nonzero_minimizer
    {β γ k m : ℝ} (hβ : 0 < β) (hγ : 0 < γ)
    (hm : 0 < m) (hmB : m ≤ ReyesMath.StrictBinding.mB β γ k) :
    ∃ u : PlaneState, mass u = m ∧
      energy β γ k u = constrainedInfimum β γ k m ∧ u.val ≠ 0 := by
  obtain ⟨u, huM, huE⟩ := exists_free_space_minimizer hβ hγ hm hmB
  refine ⟨u, huM, huE, ?_⟩
  intro hv
  have hzero : mass u = 0 := by
    simp [mass, ReyesMath.Sobolev.H2.M, hv]
  linarith

/-- Actual translated H² compactness for arbitrary minimizing sequences. -/
theorem free_space_minimizing_sequences_compact
    {β γ k m : ℝ} (hβ : 0 < β) (hγ : 0 < γ)
    (hm : 0 < m) (hmB : m ≤ ReyesMath.StrictBinding.mB β γ k)
    (u : ℕ → PlaneState) (hM : ∀ n, mass (u n) = m)
    (hE : Tendsto (fun n => energy β γ k (u n)) atTop
      (nhds (constrainedInfimum β γ k m))) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ y : ℕ → EuclideanSpace ℝ (Fin 2), ∃ U : PlaneState,
        mass U = m ∧ energy β γ k U = constrainedInfimum β γ k m ∧
        Tendsto (fun n => ReyesMath.Sobolev.H2.distH2
          (ReyesMath.Sobolev.H2.translate (y n) (u (φ n))) U)
          atTop (nhds 0) := by
  exact ReyesMath.WholeSpace.compactness hβ hγ hm hmB hM hE

/-- Spatial translation preserves exactly the same whole-plane mass and energy. -/
theorem free_space_translation_invariant
    (β γ k : ℝ) (y : EuclideanSpace ℝ (Fin 2)) (u : PlaneState) :
    mass (ReyesMath.Sobolev.H2.translate y u) = mass u ∧
      energy β γ k (ReyesMath.Sobolev.H2.translate y u) = energy β γ k u := by
  exact ⟨ReyesMath.Sobolev.H2.M_translate y u,
    ReyesMath.Sobolev.H2.energy_translate β γ k y u⟩

/-- The exact rational numbers encoding the frozen binary64 D4 parameters.
They certify the whole-plane *independent* minimization problem only. -/
noncomputable def frozenBeta : ℝ := 4608178181141995 / 1125899906842624
noncomputable def frozenMass : ℝ := 1432536998431173 / 562949953421312

theorem frozen_beta_positive : 0 < frozenBeta := by
  norm_num [frozenBeta]

theorem frozen_mass_positive : 0 < frozenMass := by
  norm_num [frozenMass]

theorem frozen_below_binding_threshold :
    frozenMass ≤ ReyesMath.StrictBinding.mB frozenBeta frozenBeta 1 := by
  have h := (ReyesMath.StrictBinding.frozen_parameters).1
  exact (show frozenMass < ReyesMath.StrictBinding.mB frozenBeta frozenBeta 1 by
    simpa [frozenBeta, frozenMass] using h).le

/-- The frozen parameter values lie in the proved whole-plane binding range. -/
theorem frozen_whole_plane_existence :
    ∃ u : PlaneState, mass u = frozenMass ∧
      energy frozenBeta frozenBeta 1 u =
        constrainedInfimum frozenBeta frozenBeta 1 frozenMass ∧ u.val ≠ 0 := by
  exact exists_nonzero_minimizer frozen_beta_positive frozen_beta_positive
    frozen_mass_positive frozen_below_binding_threshold

/-- Global well-posedness of the *independent* cubic–quintic flow; no
canonical curvature quotient or D4 periodic stationary solution is assumed. -/
theorem independent_global_flow (β γ k : ℝ) (hγ : 0 < γ) :
    ∀ u₀ : PlaneState, ∃! u : ℝ → PlaneState,
      ReyesMath.Sobolev.IsSolution β γ k u ∧ u 0 = u₀ :=
  (ReyesMath.OrbitalStability.global_flow (β := β) (γ := γ) (k := k) hγ).1

/-- Whole-plane orbital stability under general complex H² perturbations,
including perturbations whose initial mass differs from the minimizing mass. -/
theorem independent_orbital_stability
    {β γ k m : ℝ} (hβ : 0 < β) (hγ : 0 < γ)
    (hm : 0 < m) (hmB : m ≤ ReyesMath.StrictBinding.mB β γ k)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ u : ℝ → PlaneState,
      ReyesMath.Sobolev.IsSolution β γ k u →
      ReyesMath.OrbitalStability.distX (u 0)
        (ReyesMath.OrbitalStability.Gset β γ k m) < δ →
      BddAbove (Set.range fun t =>
        ReyesMath.OrbitalStability.distX (u t)
          (ReyesMath.OrbitalStability.Gset β γ k m)) ∧
      ⨆ t, ReyesMath.OrbitalStability.distX (u t)
        (ReyesMath.OrbitalStability.Gset β γ k m) < ε := by
  exact ReyesMath.OrbitalStability.orbital_stability hβ hγ hm hmB hε

/-- Exact frozen D4 *parameters* on ℝ², not stability of the torus D4 root. -/
theorem frozen_whole_plane_orbital_stability
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ u : ℝ → PlaneState,
      ReyesMath.Sobolev.IsSolution frozenBeta frozenBeta 1 u →
      ReyesMath.OrbitalStability.distX (u 0)
        (ReyesMath.OrbitalStability.Gset
          frozenBeta frozenBeta 1 frozenMass) < δ →
      BddAbove (Set.range fun t =>
        ReyesMath.OrbitalStability.distX (u t)
          (ReyesMath.OrbitalStability.Gset
            frozenBeta frozenBeta 1 frozenMass)) ∧
      ⨆ t, ReyesMath.OrbitalStability.distX (u t)
        (ReyesMath.OrbitalStability.Gset
          frozenBeta frozenBeta 1 frozenMass) < ε := by
  exact independent_orbital_stability frozen_beta_positive
    frozen_beta_positive frozen_mass_positive frozen_below_binding_threshold hε

#print axioms WCTLean.Continuum.frozen_whole_plane_existence
#print axioms WCTLean.Continuum.independent_global_flow
#print axioms WCTLean.Continuum.frozen_whole_plane_orbital_stability

end WCTLean.Continuum
