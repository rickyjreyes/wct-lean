import Mathlib
import WCTLean.Models.S004ClassicalDensity

/-!
# Phase XXIII: genuine classical two-real-component field jets

Unlike arbitrary independent jets, these jets arise from two scalar
field functions on a real (time,space) cylinder. First/second
ordinary temporal derivatives and first/second ordinary spatial
derivatives are certified by actual HasDerivAt witnesses. Their
joint continuity is part of the explicit classical C²-type class.

The class is CLOSED under affine perturbations: this module proves
that all ten jet entries shift exactly as actual derivatives of
the SAME underlying varied field. Original corrected S004
finite-cell action integrability follows from the preceding proved
classical density theorem, without an integrability assumption.

A full function-space automatic derivative construction (e.g. from
ContDiff or H^s membership), periodic boundary traces, nonlinear
domination for differentiation under the integral and critical-point
equivalence remain separate. No independent S004 surrogate is defined.
-/

open MeasureTheory Set

namespace WCTLean.S004ClassicalField

open WCTLean.S004FullSpatialJet
open WCTLean.S004ClassicalDensity
open WCTLean.S004ContinuousEuler

/-- Two time derivatives and two spatial derivatives of ONE scalar
field, with actual real-line derivative certificates and joint
continuity of the resulting coordinate functions. -/
structure ClassicalScalarField where
  field : ℝ × ℝ → ℝ
  dt : ℝ × ℝ → ℝ
  dtt : ℝ × ℝ → ℝ
  dx : ℝ × ℝ → ℝ
  dxx : ℝ × ℝ → ℝ
  time1 : ∀ t x,
    HasDerivAt (fun s => field (s,x)) (dt (t,x)) t
  time2 : ∀ t x,
    HasDerivAt (fun s => dt (s,x)) (dtt (t,x)) t
  space1 : ∀ t x,
    HasDerivAt (fun s => field (t,s)) (dx (t,x)) x
  space2 : ∀ t x,
    HasDerivAt (fun s => dx (t,s)) (dxx (t,x)) x
  cont_field : Continuous field
  cont_dt : Continuous dt
  cont_dtt : Continuous dtt
  cont_dx : Continuous dx
  cont_dxx : Continuous dxx

/-- The affine variation stays in the SAME physically compatible
classical derivative class. Every derivative certificate follows
from the true derivative linearity rules, not an abstract operator. -/
def scalarShift (u h : ClassicalScalarField) (k : ℝ) :
    ClassicalScalarField where
  field := fun z => u.field z + k * h.field z
  dt := fun z => u.dt z + k * h.dt z
  dtt := fun z => u.dtt z + k * h.dtt z
  dx := fun z => u.dx z + k * h.dx z
  dxx := fun z => u.dxx z + k * h.dxx z
  time1 := by
    intro t x
    exact (u.time1 t x).add ((h.time1 t x).const_mul k)
  time2 := by
    intro t x
    exact (u.time2 t x).add ((h.time2 t x).const_mul k)
  space1 := by
    intro t x
    exact (u.space1 t x).add ((h.space1 t x).const_mul k)
  space2 := by
    intro t x
    exact (u.space2 t x).add ((h.space2 t x).const_mul k)
  cont_field := u.cont_field.add (continuous_const.mul h.cont_field)
  cont_dt := u.cont_dt.add (continuous_const.mul h.cont_dt)
  cont_dtt := u.cont_dtt.add (continuous_const.mul h.cont_dtt)
  cont_dx := u.cont_dx.add (continuous_const.mul h.cont_dx)
  cont_dxx := u.cont_dxx.add (continuous_const.mul h.cont_dxx)

/-- The actual original corrected S004 real/imaginary field jet
for one periodic spatial dimension. All higher entries are the
specified second derivatives of the same underlying scalar field. -/
def genuineJet (uR uI : ClassicalScalarField)
    (z : ℝ × ℝ) : Jet 1 where
  x := uR.field z
  y := uI.field z
  vx := uR.dt z
  vy := uI.dt z
  ax := uR.dtt z
  ay := uI.dtt z
  bx := uR.dxx z
  bY := uI.dxx z
  gx := fun _ => uR.dx z
  gy := fun _ => uI.dx z

/-- The genuine time-derivative jets satisfy BOTH first and
second temporal derivative relations for BOTH physical real
field components, at every spacetime point. -/
theorem genuine_jet_temporal_compatibility
    (uR uI : ClassicalScalarField) (t x : ℝ) :
    HasDerivAt (fun s => (genuineJet uR uI (s,x)).x)
      (genuineJet uR uI (t,x)).vx t ∧
    HasDerivAt (fun s => (genuineJet uR uI (s,x)).y)
      (genuineJet uR uI (t,x)).vy t ∧
    HasDerivAt (fun s => (genuineJet uR uI (s,x)).vx)
      (genuineJet uR uI (t,x)).ax t ∧
    HasDerivAt (fun s => (genuineJet uR uI (s,x)).vy)
      (genuineJet uR uI (t,x)).ay t := by
  exact ⟨uR.time1 t x, uI.time1 t x, uR.time2 t x, uI.time2 t x⟩

/-- The spatial first derivative and Laplacian (second derivative
in 1+1) are likewise actual derivatives of the same fields. -/
theorem genuine_jet_spatial_compatibility
    (uR uI : ClassicalScalarField) (t x : ℝ) :
    HasDerivAt (fun s => (genuineJet uR uI (t,s)).x)
      ((genuineJet uR uI (t,x)).gx 0) x ∧
    HasDerivAt (fun s => (genuineJet uR uI (t,s)).y)
      ((genuineJet uR uI (t,x)).gy 0) x ∧
    HasDerivAt (fun s => (genuineJet uR uI (t,s)).gx 0)
      (genuineJet uR uI (t,x)).bx x ∧
    HasDerivAt (fun s => (genuineJet uR uI (t,s)).gy 0)
      (genuineJet uR uI (t,x)).bY x := by
  exact ⟨uR.space1 t x, uI.space1 t x, uR.space2 t x, uI.space2 t x⟩

/-- The nonlinear S004 jet perturbation is EXACTLY the jet of the
affinely perturbed underlying scalar fields. All ten independent
coordinate equalities hold, no PDE or artificial linear operator. -/
theorem genuine_jet_shift
    (uR uI hR hI : ClassicalScalarField) (k : ℝ)
    (z : ℝ × ℝ) :
    genuineJet (scalarShift uR hR k) (scalarShift uI hI k) z =
      shift (genuineJet uR uI z) (genuineJet hR hI z) k := by
  rfl

/-- Each genuine two-real-component classical jet satisfies the
concrete ten-component joint continuity condition. -/
theorem genuine_jet_continuous
    (uR uI : ClassicalScalarField) :
    ContinuousJet (genuineJet uR uI) := by
  exact {
    x := uR.cont_field
    y := uI.cont_field
    vx := uR.cont_dt
    vy := uI.cont_dt
    ax := uR.cont_dtt
    ay := uI.cont_dtt
    bx := uR.cont_dxx
    bY := uI.cont_dxx
    gx := uR.cont_dx
    gy := uI.cont_dx
  }

/-- The exact original nonlinear S004 action density of TWO
genuine compatible classical scalar fields and any genuine
classical variation is Lebesgue integrable for EVERY perturbation
parameter, including through field zeros. -/
theorem genuine_action_all_shifts_integrable
    (a b c d epsilon alpha kappa theta gamma : ℝ)
    (hab : a ≤ b) (hcd : c ≤ d)
    (heps : 0 < epsilon) (ha : 0 ≤ alpha)
    (V : ℝ → ℝ) (hV : Continuous V)
    (uR uI hR hI : ClassicalScalarField) :
    ∀ k : ℝ,
      Integrable
        (fun z => fullLocalDensity epsilon alpha kappa theta gamma V
          (genuineJet (scalarShift uR hR k)
            (scalarShift uI hI k) z))
        (rectangleVolume a b c d) := by
  intro k
  have h := integrable_fullLocalDensity_all_shifts
    a b c d epsilon alpha kappa theta gamma
    hab hcd heps ha V hV
    (genuineJet uR uI) (genuineJet hR hI)
    (genuine_jet_continuous uR uI)
    (genuine_jet_continuous hR hI) k
  simpa only [genuine_jet_shift] using h

end WCTLean.S004ClassicalField
