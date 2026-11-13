import Mathlib
import WCTLean.Models.S004TwoComponentVariation
import WCTLean.Models.S004PrincipalDegeneracy

/-!
# Phase XXIV: the exact S004 field-node expansion

The original corrected nonlinear action's curvature contribution is
quartic along any common affine scaling of the two real field
components AND their time/space derivative jets from the zero jet.

This gives a precise mathematical warning: an ordinary quadratic
vacuum expansion cannot detect the higher-derivative curvature
contribution, although the nonzero-field regular canonical sector has
an independently proved Ostrogradsky obstruction.

The statements below are original-model local jet theorems. They do
not prove global PDE evolution, nonlinear stability, constraint
preservation, or existence of localized nonzero solutions.
-/

namespace WCTLean.S004VacuumOnset

open WCTLean
open WCTLean.S004TwoComponent
open WCTLean.S004JetVariation

/-- The identically zero two-real-component physical field jet. -/
def vacuumJet : Jet where
  x := 0
  y := 0
  vx := 0
  vy := 0
  gx := 0
  gy := 0
  ax := 0
  ay := 0
  bx := 0
  bY := 0

/-- The squared field amplitude is quadratic along every
real-amplitude path through the exact field node. -/
theorem vacuum_density_exact_quadratic (h : Jet) (t : ℝ) :
    realTwoComponentDensity (t * h.x) (t * h.y) =
      t ^ 2 * realTwoComponentDensity h.x h.y := by
  unfold realTwoComponentDensity
  ring

/-- The actual S004 acceleration/Laplacian curvature form is
quadratic when every derivative jet is scaled from zero. -/
theorem vacuum_curvature_form_exact_quadratic
    (kappa theta gamma : ℝ) (h : Jet) (t : ℝ) :
    curvatureForm kappa theta gamma (vacuumJet.shift h t) =
      t ^ 2 * curvatureForm kappa theta gamma h := by
  simp [curvatureForm, curvatureQuadratic, Jet.shift, vacuumJet]
  ring

/-- The ORIGINAL corrected S004 nonlinear curvature term has a
fourth-order numerator about the vacuum. The denominator is the
original corrected regularizer, not a frozen coefficient.

Consequently a quadratic expansion at the vacuum misses this
higher-derivative term. This is not a claim that the full nonlinear
regular sector is ghost free. -/
theorem vacuum_curvature_term_exact_quartic
    (epsilon alpha kappa theta gamma : ℝ) (h : Jet) (t : ℝ) :
    realTwoComponentWeight epsilon alpha (t * h.x) (t * h.y) *
        curvatureForm kappa theta gamma (vacuumJet.shift h t) =
      (t ^ 4 * realTwoComponentDensity h.x h.y *
          curvatureForm kappa theta gamma h) /
        (correctedRadialDenominator epsilon alpha
          (t ^ 2 * realTwoComponentDensity h.x h.y)) ^ 2 := by
  rw [vacuum_curvature_form_exact_quadratic,
    realTwoComponentWeight, vacuum_density_exact_quadratic,
    correctedRadialWeight]
  ring

/-- The first directional derivative of the original nonlinear
S004 local action vanishes at the identically zero physical jet
for EVERY independent two-real-component perturbation jet. -/
theorem vacuum_local_direction_zero
    (epsilon alpha kappa theta gamma Vprime : ℝ) (h : Jet) :
    localDirection epsilon alpha kappa theta gamma Vprime
      vacuumJet h = 0 := by
  simp [localDirection, vacuumJet, realTwoComponentWeight,
    realTwoComponentDensity, correctedRadialWeight]

/-- A true first-variation statement, derived from the original
corrected composite S004 local density. The potential is only
required to have a derivative at the zero squared amplitude.
The absence of a linear vacuum term does NOT establish nonlinear
PDE stability. -/
theorem vacuum_localDensity_hasDerivAt_zero
    (epsilon alpha kappa theta gamma : ℝ)
    (V : ℝ → ℝ) (Vprime : ℝ) (h : Jet)
    (heps : 0 < epsilon) (ha : 0 ≤ alpha)
    (hV : HasDerivAt V Vprime 0) :
    HasDerivAt
      (fun t : ℝ => localDensity epsilon alpha kappa theta gamma
        V (vacuumJet.shift h t)) 0 0 := by
  have hV0 : HasDerivAt V Vprime
      (realTwoComponentDensity vacuumJet.x vacuumJet.y) := by
    simpa [vacuumJet, realTwoComponentDensity] using hV
  have hder := localDensity_hasDerivAt
    epsilon alpha kappa theta gamma V vacuumJet h Vprime
    heps ha hV0
  rw [vacuum_local_direction_zero] at hder
  exact hder

end WCTLean.S004VacuumOnset
