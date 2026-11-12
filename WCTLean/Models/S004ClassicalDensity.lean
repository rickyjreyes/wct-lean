import Mathlib
import WCTLean.Models.S004ContinuousAdmissibility
import WCTLean.Models.S004FullSpatialIntegratedVariation

/-!
# Phase XXIII: actual continuous classical S004 density, all shifted actions

A concrete classical 1+1 finite-cell jet regularity class requires
continuity of the *ten original physical components* of the real/imag
jet (field, velocity, acceleration, spatial gradient and Laplacian).
The original corrected nonlinear S004 density then is continuous,
including across field nodes, when V is continuous and the original
positive regulator assumptions hold.

This proves actual Lebesgue integrability of the original action
density and of every shifted action density for any two continuous
jets. It removes two previously independent ActionDomination
premises (measurability and base-point integrability). The derivative
jets are not yet constructed from a C^k or Sobolev field and the
uniform Lipschitz bound for differentiating under the integral
remains open. No separate model or invented regulator is introduced.
-/

open MeasureTheory Set Filter Topology

namespace WCTLean.S004ClassicalDensity

open WCTLean
open WCTLean.S004FullSpatialJet
open WCTLean.S004TwoComponent
open WCTLean.S004JetVariation
open WCTLean.S004ContinuousAdmissibility
open WCTLean.S004ContinuousEuler
open WCTLean.S004SpacetimeFubini

/-- A concrete *classical jet continuity* hypothesis on the ten
original S004 scalar components. The jet entries are not presumed
to satisfy derivative compatibility merely from continuity. -/
structure ContinuousJet (u : ℝ × ℝ → Jet 1) : Prop where
  x : Continuous (fun z => (u z).x)
  y : Continuous (fun z => (u z).y)
  vx : Continuous (fun z => (u z).vx)
  vy : Continuous (fun z => (u z).vy)
  ax : Continuous (fun z => (u z).ax)
  ay : Continuous (fun z => (u z).ay)
  bx : Continuous (fun z => (u z).bx)
  bY : Continuous (fun z => (u z).bY)
  gx : Continuous (fun z => (u z).gx 0)
  gy : Continuous (fun z => (u z).gy 0)

/-- All ten coordinates of the actual jet shift are continuous
simultaneously. This is the exact same shift used in the original
S004 first-variation theorem, not an independently defined path. -/
theorem continuous_shift
    (u h : ℝ × ℝ → Jet 1)
    (hu : ContinuousJet u) (hh : ContinuousJet h)
    (t : ℝ) :
    ContinuousJet (fun z => shift (u z) (h z) t) := by
  refine {
    x := ?_
    y := ?_
    vx := ?_
    vy := ?_
    ax := ?_
    ay := ?_
    bx := ?_
    bY := ?_
    gx := ?_
    gy := ?_
  }
  · simpa only [shift] using hu.x.add (continuous_const.mul hh.x)
  · simpa only [shift] using hu.y.add (continuous_const.mul hh.y)
  · simpa only [shift] using hu.vx.add (continuous_const.mul hh.vx)
  · simpa only [shift] using hu.vy.add (continuous_const.mul hh.vy)
  · simpa only [shift] using hu.ax.add (continuous_const.mul hh.ax)
  · simpa only [shift] using hu.ay.add (continuous_const.mul hh.ay)
  · simpa only [shift] using hu.bx.add (continuous_const.mul hh.bx)
  · simpa only [shift] using hu.bY.add (continuous_const.mul hh.bY)
  · simpa only [shift] using hu.gx.add (continuous_const.mul hh.gx)
  · simpa only [shift] using hu.gy.add (continuous_const.mul hh.gy)

/-- The original higher-order curvature quadratic is continuous
for continuous acceleration and Laplacian jets. -/
theorem continuous_curvature_of_jet
    (kappa theta gamma : ℝ) (u : ℝ × ℝ → Jet 1)
    (hu : ContinuousJet u) :
    Continuous (fun z =>
      curvatureForm kappa theta gamma (core (u z))) := by
  have hR : Continuous (fun z =>
      curvatureQuadratic kappa theta gamma (u z).ax (u z).bx) := by
    unfold curvatureQuadratic
    exact ((continuous_const.mul ((hu.bx.sub hu.ax).pow 2)).add
      (continuous_const.mul (hu.bx.pow 2))).add
        (continuous_const.mul ((hu.bx.sub hu.ax).mul hu.bx))
  have hI : Continuous (fun z =>
      curvatureQuadratic kappa theta gamma (u z).ay (u z).bY) := by
    unfold curvatureQuadratic
    exact ((continuous_const.mul ((hu.bY.sub hu.ay).pow 2)).add
      (continuous_const.mul (hu.bY.pow 2))).add
        (continuous_const.mul ((hu.bY.sub hu.ay).mul hu.bY))
  change Continuous (fun z =>
    curvatureQuadratic kappa theta gamma (u z).ax (u z).bx +
    curvatureQuadratic kappa theta gamma (u z).ay (u z).bY)
  exact hR.add hI

/-- The TRUE original corrected S004 density is continuous on
spacetime for every continuous classical jet, including at
psi=0. No assumption of nonzero field amplitude is needed. -/
theorem continuous_fullLocalDensity
    (epsilon alpha kappa theta gamma : ℝ)
    (heps : 0 < epsilon) (ha : 0 ≤ alpha)
    (V : ℝ → ℝ) (hV : Continuous V)
    (u : ℝ × ℝ → Jet 1) (hu : ContinuousJet u) :
    Continuous (fun z =>
      fullLocalDensity epsilon alpha kappa theta gamma V (u z)) := by
  have hweight : Continuous (fun z =>
      realTwoComponentWeight epsilon alpha (u z).x (u z).y) :=
    corrected_weight_continuous_for_field epsilon alpha heps ha
      (fun z => (u z).x) (fun z => (u z).y) hu.x hu.y
  have hrho : Continuous (fun z =>
      realTwoComponentDensity (u z).x (u z).y) := by
    simpa only [realTwoComponentDensity] using (hu.x.pow 2).add (hu.y.pow 2)
  have hpot : Continuous (fun z =>
      V (realTwoComponentDensity (u z).x (u z).y)) :=
    hV.comp hrho
  have hcurv := continuous_curvature_of_jet kappa theta gamma u hu
  have hgrad : Continuous (fun z =>
      ∑ i : Fin 1, ((u z).gx i ^ 2 + (u z).gy i ^ 2)) := by
    simpa [Fin.sum_univ_one] using (hu.gx.pow 2).add (hu.gy.pow 2)
  have hvel : Continuous (fun z =>
      -((u z).vx ^ 2 + (u z).vy ^ 2)) :=
    ((hu.vx.pow 2).add (hu.vy.pow 2)).neg
  have htotal : Continuous (fun z =>
      (-((u z).vx ^ 2 + (u z).vy ^ 2) +
       ∑ i : Fin 1, ((u z).gx i ^ 2 + (u z).gy i ^ 2)) -
       V (realTwoComponentDensity (u z).x (u z).y) +
       realTwoComponentWeight epsilon alpha (u z).x (u z).y *
         curvatureForm kappa theta gamma (core (u z))) :=
    ((hvel.add hgrad).sub hpot).add (hweight.mul hcurv)
  convert htotal using 1
  funext z
  simp only [fullLocalDensity, localDensity, core]
  ring

/-- The real original nonlinear S004 action integrand on a
bounded rectangle is Lebesgue integrable automatically for
continuous classical jets. This is not a formal integral
on arbitrary symbolic operators. -/
theorem integrable_fullLocalDensity_on_rectangle
    (a b c d epsilon alpha kappa theta gamma : ℝ)
    (hab : a ≤ b) (hcd : c ≤ d)
    (heps : 0 < epsilon) (ha : 0 ≤ alpha)
    (V : ℝ → ℝ) (hV : Continuous V)
    (u : ℝ × ℝ → Jet 1) (hu : ContinuousJet u) :
    Integrable
      (fun z => fullLocalDensity epsilon alpha kappa theta gamma V (u z))
      (rectangleVolume a b c d) := by
  exact continuous_rectangle_integrable a b c d hab hcd
    (fun t x => fullLocalDensity epsilon alpha kappa theta gamma
      V (u (t,x)))
    (continuous_fullLocalDensity epsilon alpha kappa theta gamma
      heps ha V hV u hu)

/-- Every genuine shifted S004 action density is integrable on
the same finite rectangle, without invoking an assumed
integrability predicate for each perturbation parameter. -/
theorem integrable_fullLocalDensity_all_shifts
    (a b c d epsilon alpha kappa theta gamma : ℝ)
    (hab : a ≤ b) (hcd : c ≤ d)
    (heps : 0 < epsilon) (ha : 0 ≤ alpha)
    (V : ℝ → ℝ) (hV : Continuous V)
    (u h : ℝ × ℝ → Jet 1)
    (hu : ContinuousJet u) (hh : ContinuousJet h) :
    ∀ t : ℝ,
      Integrable
        (fun z => fullLocalDensity epsilon alpha kappa theta gamma V
          (shift (u z) (h z) t))
        (rectangleVolume a b c d) := by
  intro t
  exact integrable_fullLocalDensity_on_rectangle
    a b c d epsilon alpha kappa theta gamma hab hcd heps ha
    V hV _ (continuous_shift u h hu hh t)

end WCTLean.S004ClassicalDensity
