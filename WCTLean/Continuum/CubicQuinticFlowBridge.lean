import WCTLean.Continuum.CubicQuinticWholeSpace
import MathProofs.OrbitalStability

/-!
# Direct global flow, continuous-dependence and conservation bridge

This module imports full infinite-dimensional H²(ℝ²; ℂ) results for the
independent fourth-order cubic–quintic Hamiltonian. The corrected curvature
quotient is NOT this Hamiltonian's nonlinear evolution.
-/

open Filter

namespace WCTLean.Continuum

/-- Data-to-solution continuous dependence uniformly on every compact time
interval. No assumption fixes the mass of a perturbed solution. -/
theorem independent_continuous_dependence
    (β γ k : ℝ) (hγ : 0 < γ)
    (u : ℝ → PlaneState)
    (hu : ReyesMath.Sobolev.IsSolution β γ k u)
    (T ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ v : ℝ → PlaneState,
      ReyesMath.Sobolev.IsSolution β γ k v →
      ReyesMath.Sobolev.H2.distH2 (v 0) (u 0) < δ →
      ∀ t ∈ Set.Icc (-T) T,
        ReyesMath.Sobolev.H2.distH2 (v t) (u t) < ε := by
  exact (ReyesMath.OrbitalStability.global_flow
    (β := β) (γ := γ) (k := k) hγ).2.1 u hu T ε hε

/-- Every global solution preserves its actual H² mass and independent
cubic–quintic energy, with an explicit quantifier over all real times. -/
theorem independent_conservation
    (β γ k : ℝ) (hγ : 0 < γ)
    (u : ℝ → PlaneState)
    (hu : ReyesMath.Sobolev.IsSolution β γ k u)
    (t : ℝ) :
    mass (u t) = mass (u 0) ∧
    energy β γ k (u t) = energy β γ k (u 0) := by
  exact (ReyesMath.OrbitalStability.global_flow
    (β := β) (γ := γ) (k := k) hγ).2.2 u hu t

/-- Global well-posedness at the exact rational frozen CQ coefficients.
This concerns whole-space H², not the periodic D4 stationary branch. -/
theorem frozen_independent_global_flow :
    ∀ u₀ : PlaneState, ∃! u : ℝ → PlaneState,
      ReyesMath.Sobolev.IsSolution frozenBeta frozenBeta 1 u ∧
      u 0 = u₀ :=
  independent_global_flow frozenBeta frozenBeta 1 frozen_beta_positive

/-- The exact frozen independent whole-plane model conserves mass and
energy for every solution and every time. -/
theorem frozen_independent_conservation
    (u : ℝ → PlaneState)
    (hu : ReyesMath.Sobolev.IsSolution frozenBeta frozenBeta 1 u)
    (t : ℝ) :
    mass (u t) = mass (u 0) ∧
    energy frozenBeta frozenBeta 1 (u t) =
      energy frozenBeta frozenBeta 1 (u 0) :=
  independent_conservation frozenBeta frozenBeta 1 frozen_beta_positive u hu t

#print axioms WCTLean.Continuum.independent_continuous_dependence
#print axioms WCTLean.Continuum.independent_conservation
#print axioms WCTLean.Continuum.frozen_independent_global_flow
#print axioms WCTLean.Continuum.frozen_independent_conservation

end WCTLean.Continuum
