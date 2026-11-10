import Mathlib
import WCTLean.Models.S004FullSpatialIntegratedVariation

/-!
# Compatibility bridge: the S004 jets come from one underlying field

The existing exact integrated first-variation theorem accepts arbitrary
independent jet functions. A genuine field action must NOT treat
(psi, partial_t psi, partial_tt psi, grad psi, Delta psi)
as independent variations.

This file builds a SINGLE real-two-component field jet from declared
LINEAR first-order differential operators Dt and Dx_i. Its higher
jets are forced to be Dt(Dt psi) and sum_i Dx_i(Dx_i psi).
The exact action of a field perturbation psi+t*h is then shown to
coincide with the verified jet-variation action. This is substantive
differential-operator compatibility, not assumed equality of jets.

WARNING: a general linear map on field functions has not yet been
identified with a concrete Sobolev/distributional derivative on a
specific periodic domain. Choosing and verifying those concrete
operators is an unresolved #18 requirement. The theorem also retains
the genuine measurable-domination hypotheses from the existing
integral-variation result, and does not identify the Euler equation.
-/

open MeasureTheory Filter Topology Set

namespace WCTLean.S004CompatibleFields

open WCTLean.S004FullSpatialJet
open WCTLean.S004FullSpatialIntegral

/-- An abstract family of linear first-order derivative operators.
Their higher derivatives are NOT independent structure fields: both
Dt² and the spatial Laplacian are constructed by iteration. -/
structure FirstOrderOps (Ω : Type*) (d : ℕ) where
  dt : (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ)
  dx : Fin d → (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ)

/-- Second time derivative forced to be the square of the same Dt. -/
def time2 {Ω : Type*} {d : ℕ}
    (D : FirstOrderOps Ω d) (φ : Ω → ℝ) : Ω → ℝ :=
  D.dt (D.dt φ)

/-- Spatial Laplacian forced to be the sum of the squared first
spatial derivatives, not a separate arbitrary jet coordinate. -/
def laplacian {Ω : Type*} {d : ℕ}
    (D : FirstOrderOps Ω d) (φ : Ω → ℝ) : Ω → ℝ :=
  fun z => ∑ i : Fin d, (D.dx i) ((D.dx i) φ) z

/-- Affine path in the underlying scalar field, not in independent jets. -/
def fieldShift {Ω : Type*} (φ h : Ω → ℝ) (t : ℝ) : Ω → ℝ :=
  φ + t • h

theorem time2_shift {Ω : Type*} {d : ℕ}
    (D : FirstOrderOps Ω d) (φ h : Ω → ℝ) (t : ℝ) :
    time2 D (fieldShift φ h t) =
      fieldShift (time2 D φ) (time2 D h) t := by
  simp [time2, fieldShift, map_add, map_smul]

theorem laplacian_shift {Ω : Type*} {d : ℕ}
    (D : FirstOrderOps Ω d) (φ h : Ω → ℝ) (t : ℝ) :
    laplacian D (fieldShift φ h t) =
      fieldShift (laplacian D φ) (laplacian D h) t := by
  funext z
  simp only [laplacian, fieldShift, map_add, map_smul,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_add_distrib]
  simp only [Finset.mul_sum]

/-- The actual real/imaginary corrected S004 derivative jet with all
spatial first derivatives and their corresponding Laplacian. -/
def jetOf {Ω : Type*} {d : ℕ}
    (D : FirstOrderOps Ω d)
    (φx φy : Ω → ℝ) (z : Ω) : Jet d where
  x := φx z
  y := φy z
  vx := D.dt φx z
  vy := D.dt φy z
  ax := time2 D φx z
  ay := time2 D φy z
  bx := laplacian D φx z
  bY := laplacian D φy z
  gx := fun i => D.dx i φx z
  gy := fun i => D.dx i φy z

/-- **Genuine field-to-jet variation compatibility.** Every component
of the corrected S004 jet is forced to vary as the corresponding
first/second derivative of the SAME varied field. -/
theorem jetOf_fieldShift {Ω : Type*} {d : ℕ}
    (D : FirstOrderOps Ω d) (φx φy hx hy : Ω → ℝ)
    (t : ℝ) (z : Ω) :
    jetOf D (fieldShift φx hx t) (fieldShift φy hy t) z =
      shift (jetOf D φx φy z) (jetOf D hx hy z) t := by
  simp [jetOf, shift, fieldShift, time2, laplacian,
    map_add, map_smul, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, Finset.sum_add_distrib, Finset.mul_sum]

/-- The corrected S004 action of the underlying field path. In this
definition velocity, acceleration and Laplacian are constrained to
be produced by first-order operators acting on the SAME fields. -/
noncomputable def fieldAction {Ω : Type*} {d : ℕ}
    [MeasurableSpace Ω] (mu : Measure Ω) (D : FirstOrderOps Ω d)
    (epsilon alpha kappa theta gamma : ℝ) (V : ℝ → ℝ)
    (φx φy hx hy : Ω → ℝ) (t : ℝ) : ℝ :=
  ∫ z, fullLocalDensity epsilon alpha kappa theta gamma V
    (jetOf D (fieldShift φx hx t) (fieldShift φy hy t) z) ∂mu

/-- The field action is exactly the existing integrated corrected jet
action, with no independent jet perturbations allowed. -/
theorem fieldAction_eq_jetAction {Ω : Type*} {d : ℕ}
    [MeasurableSpace Ω] (mu : Measure Ω) (D : FirstOrderOps Ω d)
    (epsilon alpha kappa theta gamma : ℝ) (V : ℝ → ℝ)
    (φx φy hx hy : Ω → ℝ) (t : ℝ) :
    fieldAction mu D epsilon alpha kappa theta gamma V φx φy hx hy t =
      action mu epsilon alpha kappa theta gamma V
        (jetOf D φx φy) (jetOf D hx hy) t := by
  unfold fieldAction action
  congr 1
  funext z
  rw [jetOf_fieldShift]

/-- **A genuine field-action derivative** rather than a derivative
of ten independent jet coordinates. Analytical domination and
measurability remain explicitly stated, and the derivative
operators are typed linear operators awaiting the concrete
Sobolev/periodic realization. -/
theorem fieldAction_hasDerivAt_of_dominated
    {Ω : Type*} {d : ℕ} [MeasurableSpace Ω]
    (mu : Measure Ω) (D : FirstOrderOps Ω d)
    (epsilon alpha kappa theta gamma : ℝ) (V : ℝ → ℝ)
    (φx φy hx hy : Ω → ℝ) (Vprime bound : Ω → ℝ)
    (heps : 0 < epsilon) (ha : 0 ≤ alpha)
    (hV : ∀ᵐ z ∂mu, HasDerivAt V (Vprime z)
      (WCTLean.realTwoComponentDensity
        (jetOf D φx φy z).x (jetOf D φx φy z).y))
    (hmeas : ∀ᶠ t in 𝓝 (0 : ℝ),
      AEStronglyMeasurable
        (fun z => fullLocalDensity epsilon alpha kappa theta gamma
          V (shift (jetOf D φx φy z) (jetOf D hx hy z) t)) mu)
    (hint : Integrable
      (fun z => fullLocalDensity epsilon alpha kappa theta gamma
        V (shift (jetOf D φx φy z) (jetOf D hx hy z) (0 : ℝ))) mu)
    (hdmeas : AEStronglyMeasurable
      (fun z => fullLocalDirection epsilon alpha kappa theta gamma
        (Vprime z) (jetOf D φx φy z) (jetOf D hx hy z)) mu)
    (hboundInt : Integrable bound mu)
    (hlip : ∀ᵐ z ∂mu,
      LipschitzOnWith (Real.nnabs (bound z))
        (fun t : ℝ => fullLocalDensity epsilon alpha kappa theta gamma
          V (shift (jetOf D φx φy z) (jetOf D hx hy z) t))
        (Metric.ball (0 : ℝ) 1)) :
    HasDerivAt
      (fieldAction mu D epsilon alpha kappa theta gamma V φx φy hx hy)
      (∫ z, fullLocalDirection epsilon alpha kappa theta gamma
        (Vprime z) (jetOf D φx φy z) (jetOf D hx hy z) ∂mu) 0 := by
  have h := (action_hasDerivAt_of_dominated
    mu epsilon alpha kappa theta gamma V
    (jetOf D φx φy) (jetOf D hx hy)
    Vprime bound heps ha hV hmeas hint hdmeas hboundInt hlip).2
  have hfun :
      fieldAction mu D epsilon alpha kappa theta gamma V φx φy hx hy =
      action mu epsilon alpha kappa theta gamma V
        (jetOf D φx φy) (jetOf D hx hy) := by
    funext t
    exact fieldAction_eq_jetAction mu D
      epsilon alpha kappa theta gamma V φx φy hx hy t
  rw [hfun]
  exact h

end WCTLean.S004CompatibleFields
