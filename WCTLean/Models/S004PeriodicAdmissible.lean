import Mathlib
import WCTLean.Models.S004ClassicalPeriodicity
import WCTLean.Models.S004ClassicalField

/-!
# Phase XXII: an affine-closed periodic classical field class for S004

This module packages a genuine C²-type scalar field and its spatial
translation identity into one reusable admissibility object. The
class is preserved by the exact original S004 affine field variation.
It supplies all ten periodic physical jet identities and automatic
integrability for the original regulated action on a finite cell.

This does not assert nonlinear momentum Green regularity,
Sobolev mapping/density, derivative domination or ghost freedom.
-/

namespace WCTLean.S004PeriodicAdmissible

open WCTLean.S004ClassicalField
open WCTLean.S004ClassicalPeriodicity
open WCTLean.S004FullSpatialJet
open WCTLean.S004ContinuousEuler

/-- The same genuine scalar field derivatives used in the original
S004 action, with one exact spatial period. -/
structure PeriodicScalarField (L : ℝ) where
  toClassical : ClassicalScalarField
  periodic : ∀ t x, toClassical.field (t, x + L) = toClassical.field (t, x)

/-- Affine variations preserve the original periodicity and retain
the true derivative certificates of the underlying classical fields. -/
def affineShift {L : ℝ} (u h : PeriodicScalarField L) (k : ℝ) :
    PeriodicScalarField L where
  toClassical := scalarShift u.toClassical h.toClassical k
  periodic := by
    intro t x
    change u.toClassical.field (t, x + L) +
        k * h.toClassical.field (t, x + L) =
      u.toClassical.field (t, x) + k * h.toClassical.field (t, x)
    rw [u.periodic t x, h.periodic t x]

/-- Spatial periodicity of the field entails the matching values,
first/second temporal derivatives and first/second spatial derivatives.
No independent jet endpoint conditions are postulated. -/
theorem all_classical_traces {L : ℝ} (u : PeriodicScalarField L) :
    ∀ t x,
      u.toClassical.field (t, x + L) = u.toClassical.field (t, x) ∧
      u.toClassical.dt (t, x + L) = u.toClassical.dt (t, x) ∧
      u.toClassical.dtt (t, x + L) = u.toClassical.dtt (t, x) ∧
      u.toClassical.dx (t, x + L) = u.toClassical.dx (t, x) ∧
      u.toClassical.dxx (t, x + L) = u.toClassical.dxx (t, x) := by
  exact classical_all_five_jets_periodic
    u.toClassical L u.periodic

/-- The original two-component physical jet is exactly the affine
perturbation of the underlying periodic fields. -/
theorem genuine_periodic_jet_shift {L : ℝ}
    (uR uI hR hI : PeriodicScalarField L) (k : ℝ)
    (z : ℝ × ℝ) :
    genuineJet (affineShift uR hR k).toClassical
        (affineShift uI hI k).toClassical z =
      shift (genuineJet uR.toClassical uI.toClassical z)
        (genuineJet hR.toClassical hI.toClassical z) k := by
  exact genuine_jet_shift uR.toClassical uI.toClassical
    hR.toClassical hI.toClassical k z

/-- Original corrected S004 density is integrable for every affine
variation of genuine periodic classical fields on the actual finite
Lebesgue spacetime cell, including when the field vanishes. -/
theorem periodic_genuine_action_all_shifts_integrable
    (a b c d epsilon alpha kappa theta gamma L : ℝ)
    (hab : a ≤ b) (hcd : c ≤ d)
    (heps : 0 < epsilon) (ha : 0 ≤ alpha)
    (V : ℝ → ℝ) (hV : Continuous V)
    (uR uI hR hI : PeriodicScalarField L) :
    ∀ k : ℝ,
      MeasureTheory.Integrable
        (fun z => fullLocalDensity epsilon alpha kappa theta gamma V
          (genuineJet
            (affineShift uR hR k).toClassical
            (affineShift uI hI k).toClassical z))
        (rectangleVolume a b c d) := by
  intro k
  exact genuine_action_all_shifts_integrable
    a b c d epsilon alpha kappa theta gamma
    hab hcd heps ha V hV
    uR.toClassical uI.toClassical hR.toClassical hI.toClassical k

end WCTLean.S004PeriodicAdmissible
