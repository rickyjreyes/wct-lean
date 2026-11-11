import Mathlib
import WCTLean.Models.S004SpacetimeGreen
import WCTLean.Models.S004EulerCoefficients

/-!
# One-dimensional periodic S004: combined spacetime weak Euler identity

Unlike earlier separate 1D temporal and spatial formulas, this is
ONE theorem about the original S004 corrected action's true
two-dimensional (time × periodic-space) Euler momenta.

The two field components are indexed by Bool. All five S004
coefficient families are the literal nonlinear corrected coefficients:
field force with the full F' term, velocity momentum, acceleration
momentum, spatial-gradient momentum and Laplacian momentum.

Under actual classical derivative, boundary-trace, integrability and
product-measure Fubini premises, the proof applies four GENUINE
2D continuum Green identities to transform the weak directional
functional into an explicit strong Euler expression. No
integration-by-parts equality is assumed.

The weak functional here is a SUM OF FIVE ITERATED INTEGRALS;
the remaining bridge to the already proved single action-derivative
integral requires termwise integrability/linearity and explicit
realization of the jet as Sobolev derivatives.
-/

open MeasureTheory Set
open scoped Interval

namespace WCTLean.S004SpacetimeEuler

open WCTLean.S004FullSpatialJet
open WCTLean.S004EulerCoefficients
open WCTLean.S004SpacetimeGreen

/-- Selector for one of the two REAL components of the original
complex scalar field (not a scalar replacement theory). -/
def component (side : Bool) (u : Jet 1) : ℝ :=
  if side then u.x else u.y

def velocity (side : Bool) (u : Jet 1) : ℝ :=
  if side then u.vx else u.vy

def acceleration (side : Bool) (u : Jet 1) : ℝ :=
  if side then u.ax else u.ay

def gradient (side : Bool) (u : Jet 1) : ℝ :=
  if side then u.gx 0 else u.gy 0

def laplacian (side : Bool) (u : Jet 1) : ℝ :=
  if side then u.bx else u.bY

/-- Actual corrected local potential/curvature force. -/
noncomputable def force (side : Bool)
    (epsilon alpha kappa theta gamma Vprime : ℝ)
    (u : Jet 1) : ℝ :=
  if side then forceX epsilon alpha kappa theta gamma Vprime u
  else forceY epsilon alpha kappa theta gamma Vprime u

/-- Actual negative velocity-square momentum. -/
def timeMomentum (side : Bool) (u : Jet 1) : ℝ :=
  -2 * velocity side u

/-- Actual corrected nonlinear acceleration momentum. -/
noncomputable def accelerationMomentum (side : Bool)
    (epsilon alpha kappa gamma : ℝ) (u : Jet 1) : ℝ :=
  if side then accelX epsilon alpha kappa gamma u
  else accelY epsilon alpha kappa gamma u

/-- Original positive spatial-gradient quadratic momentum. -/
def gradientMomentum (side : Bool) (u : Jet 1) : ℝ :=
  2 * gradient side u

/-- Original nonlinear mixed curvature Laplacian momentum. -/
noncomputable def laplacianMomentum (side : Bool)
    (epsilon alpha kappa theta gamma : ℝ) (u : Jet 1) : ℝ :=
  if side then lapX epsilon alpha kappa theta gamma u
  else lapY epsilon alpha kappa theta gamma u

/-- The one-component weak S004 variation as FIVE genuine
time-major interval iterated integrals, not a formal dot product. -/
noncomputable def weakComponent (side : Bool)
    (a b c d epsilon alpha kappa theta gamma : ℝ)
    (Vprime : ℝ → ℝ → ℝ)
    (u h : ℝ → ℝ → Jet 1) : ℝ :=
  (∫ t in a..b, ∫ x in c..d,
    force side epsilon alpha kappa theta gamma (Vprime t x)
      (u t x) * component side (h t x)) +
  (∫ t in a..b, ∫ x in c..d,
    timeMomentum side (u t x) * velocity side (h t x)) +
  (∫ t in a..b, ∫ x in c..d,
    accelerationMomentum side epsilon alpha kappa gamma (u t x) *
      acceleration side (h t x)) +
  (∫ t in a..b, ∫ x in c..d,
    gradientMomentum side (u t x) * gradient side (h t x)) +
  (∫ t in a..b, ∫ x in c..d,
    laplacianMomentum side epsilon alpha kappa theta gamma (u t x) *
      laplacian side (h t x))

/-- Full 1+1-dimensional strong Euler pairing, with the original
nonlinear force, actual first/second time momentum derivatives, and
actual first/second periodic spatial momentum derivatives. -/
noncomputable def strongComponent (side : Bool)
    (a b c d epsilon alpha kappa theta gamma : ℝ)
    (Vprime : ℝ → ℝ → ℝ)
    (u h : ℝ → ℝ → Jet 1)
    (time1 accel2 grad1 lap2 : ℝ → ℝ → ℝ) : ℝ :=
  (∫ t in a..b, ∫ x in c..d,
    force side epsilon alpha kappa theta gamma (Vprime t x)
      (u t x) * component side (h t x)) -
  (∫ t in a..b, ∫ x in c..d,
    time1 t x * component side (h t x)) +
  (∫ t in a..b, ∫ x in c..d,
    accel2 t x * component side (h t x)) -
  (∫ t in a..b, ∫ x in c..d,
    grad1 t x * component side (h t x)) +
  (∫ t in a..b, ∫ x in c..d,
    lap2 t x * component side (h t x))

/-- **Combined original S004 weak-to-strong spacetime Euler theorem.**

The hypotheses are actual componentwise classical derivative equations,
interval integrability, PRODUCT-MEASURE integrability for Fubini,
and true boundary trace constraints. They neither assert the desired
weak-to-strong identity nor assume a full Euler PDE.

The result combines temporal and periodic spatial differentiation
inside one 2D continuum functional with all original S004 coefficients.
-/
theorem weakComponent_eq_strongComponent
    (side : Bool)
    (a b c d epsilon alpha kappa theta gamma : ℝ)
    (hcd : c ≤ d)
    (Vprime : ℝ → ℝ → ℝ)
    (u h : ℝ → ℝ → Jet 1)
    (time1 accel1 accel2 grad1 lap1 lap2 : ℝ → ℝ → ℝ)
    (htm : ∀ x t, t ∈ [[a,b]] →
      HasDerivAt
        (fun s => timeMomentum side (u s x)) (time1 t x) t)
    (hta : ∀ x t, t ∈ [[a,b]] →
      HasDerivAt
        (fun s => accelerationMomentum side epsilon alpha kappa gamma
          (u s x)) (accel1 t x) t)
    (hta1 : ∀ x t, t ∈ [[a,b]] →
      HasDerivAt (fun s => accel1 s x) (accel2 t x) t)
    (hvt : ∀ x t, t ∈ [[a,b]] →
      HasDerivAt (fun s => component side (h s x))
        (velocity side (h t x)) t)
    (hvt1 : ∀ x t, t ∈ [[a,b]] →
      HasDerivAt (fun s => velocity side (h s x))
        (acceleration side (h t x)) t)
    (htmInt : ∀ x,
      IntervalIntegrable (fun t => time1 t x) volume a b)
    (htaInt : ∀ x,
      IntervalIntegrable (fun t => accel1 t x) volume a b)
    (hta2Int : ∀ x,
      IntervalIntegrable (fun t => accel2 t x) volume a b)
    (hvtInt : ∀ x,
      IntervalIntegrable (fun t => velocity side (h t x)) volume a b)
    (hvaInt : ∀ x,
      IntervalIntegrable (fun t => acceleration side (h t x)) volume a b)
    (hv0a : ∀ x, component side (h a x) = 0)
    (hv0b : ∀ x, component side (h b x) = 0)
    (hv1a : ∀ x, velocity side (h a x) = 0)
    (hv1b : ∀ x, velocity side (h b x) = 0)
    (hgm : ∀ t x, x ∈ [[c,d]] →
      HasDerivAt
        (fun s => gradientMomentum side (u t s)) (grad1 t x) x)
    (hlm : ∀ t x, x ∈ [[c,d]] →
      HasDerivAt
        (fun s => laplacianMomentum side epsilon alpha kappa theta gamma
          (u t s)) (lap1 t x) x)
    (hlm1 : ∀ t x, x ∈ [[c,d]] →
      HasDerivAt (fun s => lap1 t s) (lap2 t x) x)
    (hvs : ∀ t x, x ∈ [[c,d]] →
      HasDerivAt (fun s => component side (h t s))
        (gradient side (h t x)) x)
    (hvs1 : ∀ t x, x ∈ [[c,d]] →
      HasDerivAt (fun s => gradient side (h t s))
        (laplacian side (h t x)) x)
    (hgmInt : ∀ t,
      IntervalIntegrable (fun x => grad1 t x) volume c d)
    (hlmInt : ∀ t,
      IntervalIntegrable (fun x => lap1 t x) volume c d)
    (hlm2Int : ∀ t,
      IntervalIntegrable (fun x => lap2 t x) volume c d)
    (hvsInt : ∀ t,
      IntervalIntegrable (fun x => gradient side (h t x)) volume c d)
    (hvlInt : ∀ t,
      IntervalIntegrable (fun x => laplacian side (h t x)) volume c d)
    (hgmPer : ∀ t, gradientMomentum side (u t d) =
      gradientMomentum side (u t c))
    (hlmPer : ∀ t,
      laplacianMomentum side epsilon alpha kappa theta gamma (u t d) =
      laplacianMomentum side epsilon alpha kappa theta gamma (u t c))
    (hl1Per : ∀ t, lap1 t d = lap1 t c)
    (hvPer : ∀ t, component side (h t d) = component side (h t c))
    (hvgPer : ∀ t, gradient side (h t d) = gradient side (h t c))
    (hfTm : IntegrableOn
      (Function.uncurry (fun t x =>
        timeMomentum side (u t x) * velocity side (h t x)))
      (uIoc a b ×ˢ uIoc c d))
    (hgTm : IntegrableOn
      (Function.uncurry (fun t x =>
        time1 t x * component side (h t x)))
      (uIoc a b ×ˢ uIoc c d))
    (hfAcc : IntegrableOn
      (Function.uncurry (fun t x =>
        accelerationMomentum side epsilon alpha kappa gamma (u t x) *
        acceleration side (h t x)))
      (uIoc a b ×ˢ uIoc c d))
    (hgAcc : IntegrableOn
      (Function.uncurry (fun t x =>
        accel2 t x * component side (h t x)))
      (uIoc a b ×ˢ uIoc c d)) :
    weakComponent side a b c d epsilon alpha kappa theta gamma
      Vprime u h =
    strongComponent side a b c d epsilon alpha kappa theta gamma
      Vprime u h time1 accel2 grad1 lap2 := by
  have ht := temporal_first_spacetime a b c d hcd
    (fun t x => timeMomentum side (u t x)) time1
    (fun t x => component side (h t x))
    (fun t x => velocity side (h t x))
    htm hvt htmInt hvtInt hv0a hv0b hfTm hgTm
  have hta2 := temporal_second_spacetime a b c d hcd
    (fun t x => accelerationMomentum side epsilon alpha kappa gamma (u t x))
    accel1 accel2
    (fun t x => component side (h t x))
    (fun t x => velocity side (h t x))
    (fun t x => acceleration side (h t x))
    hta hta1 hvt hvt1 htaInt hta2Int hvtInt hvaInt
    hv0a hv0b hv1a hv1b hfAcc hgAcc
  have hs := spatial_first_spacetime a b c d
    (fun t x => gradientMomentum side (u t x)) grad1
    (fun t x => component side (h t x))
    (fun t x => gradient side (h t x))
    hgm hvs hgmInt hvsInt hgmPer hvPer
  have hs2 := spatial_second_spacetime a b c d
    (fun t x => laplacianMomentum side epsilon alpha kappa theta gamma (u t x))
    lap1 lap2
    (fun t x => component side (h t x))
    (fun t x => gradient side (h t x))
    (fun t x => laplacian side (h t x))
    hlm hlm1 hvs hvs1 hlmInt hlm2Int hvsInt hvlInt
    hlmPer hl1Per hvPer hvgPer
  unfold weakComponent strongComponent
  rw [ht, hta2, hs, hs2]
  ring

end WCTLean.S004SpacetimeEuler
