import Mathlib
import WCTLean.Models.S004SpacetimeEuler

/-!
# Euler residual separation by genuine L² test pairings

The S004 spacetime Green theorem now identifies an actual nonlinear
Euler residual, rather than an independent symbolic jet derivative.

The next analytical question is whether the residual is identified
uniquely by its weak pairings. Here that separation is proved for
ALL measurable test directions with integrable residual products.
The argument uses the actual Lebesgue integral of E² and its
nonnegative-integral zero characterization, NOT an assumption of
the Euler equation or a declared injectivity axiom.

The corrected S004 residual itself is instantiated below using the
verified nonlinear force, velocity/acceleration and spatial-gradient/
Laplacian momenta.

IMPORTANT: all integrable L²-type tests is a larger class than compact
temporal tests with Sobolev traces. A density theorem extending this
separation to the admissible smooth compactly-supported S004 test
space is STILL an open #17/#18 obligation. Do not confuse this lemma
with the complete original-action critical-point theorem.
-/

open MeasureTheory

namespace WCTLean.S004EulerSeparation

open WCTLean.S004SpacetimeEuler
open WCTLean.S004FullSpatialJet

/-- If E has finite L² energy, its pairing with every test direction
whose product is Lebesgue integrable vanishes IFF E itself is zero
almost everywhere. This is a proved nondegeneracy result for the
actual measure, not an abstract functional-separation axiom. -/
theorem all_integrable_probes_zero_iff_ae_zero
    {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) (E : Ω → ℝ)
    (hE2 : Integrable (fun z => E z ^ 2) mu) :
    (∀ h : Ω → ℝ,
      Integrable (fun z => E z * h z) mu →
      (∫ z, E z * h z ∂mu) = 0) ↔
      (∀ᵐ z ∂mu, E z = 0) := by
  constructor
  · intro hpair
    have hproduct : Integrable (fun z => E z * E z) mu := by
      simpa only [pow_two] using hE2
    have hself := hpair E hproduct
    have hsq : (∫ z, E z ^ 2 ∂mu) = 0 := by
      simpa only [pow_two] using hself
    have hae :=
      (MeasureTheory.integral_eq_zero_iff_of_nonneg
        (fun z => sq_nonneg (E z)) hE2).mp hsq
    filter_upwards [hae] with z hz
    have hz2 : E z ^ 2 = 0 := by simpa using hz
    nlinarith [sq_nonneg (E z)]
  · intro hzero h hint
    have hae : (fun z => E z * h z) =ᵐ[mu]
        (fun _ => (0 : ℝ)) := by
      filter_upwards [hzero] with z hz
      simp [hz]
    calc
      (∫ z, E z * h z ∂mu) =
          (∫ _z, (0 : ℝ) ∂mu) := integral_congr_ae hae
      _ = 0 := by simp

/-- Complete real/imaginary separation on an actual measure space.
This DOES NOT assume the answer E_R=E_I=0: it derives both by
independently testing the two physical field components. -/
theorem two_component_integrable_probes_iff_ae_zero
    {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) (ER EI : Ω → ℝ)
    (hER2 : Integrable (fun z => ER z ^ 2) mu)
    (hEI2 : Integrable (fun z => EI z ^ 2) mu) :
    (∀ hR hI : Ω → ℝ,
      Integrable (fun z => ER z * hR z) mu →
      Integrable (fun z => EI z * hI z) mu →
      (∫ z, ER z * hR z ∂mu) +
        (∫ z, EI z * hI z ∂mu) = 0) ↔
      (∀ᵐ z ∂mu, ER z = 0) ∧
      (∀ᵐ z ∂mu, EI z = 0) := by
  constructor
  · intro hzero
    have hR : ∀ test : Ω → ℝ,
        Integrable (fun z => ER z * test z) mu →
          (∫ z, ER z * test z ∂mu) = 0 := by
      intro test hint
      have h := hzero test (fun _ => 0) hint (by simp)
      simpa using h
    have hI : ∀ test : Ω → ℝ,
        Integrable (fun z => EI z * test z) mu →
          (∫ z, EI z * test z ∂mu) = 0 := by
      intro test hint
      have h := hzero (fun _ => 0) test (by simp) hint
      simpa using h
    exact ⟨(all_integrable_probes_zero_iff_ae_zero mu ER hER2).mp hR,
      (all_integrable_probes_zero_iff_ae_zero mu EI hEI2).mp hI⟩
  · rintro ⟨hRzero, hIzero⟩ hR hI hRint hIint
    have hR :=
      (all_integrable_probes_zero_iff_ae_zero mu ER hER2).mpr
        hRzero hR hRint
    have hI :=
      (all_integrable_probes_zero_iff_ae_zero mu EI hEI2).mpr
        hIzero hI hIint
    rw [hR, hI]
    ring

/-- The literal 1+1 corrected nonlinear S004 strong Euler residual:
the force retains F'(|psi|²) and the mixed curvature coefficients,
the derivative terms are exactly those produced by the spacetime
Green theorem. No independent toy energy or field equation. -/
noncomputable def correctedEulerResidual
    (side : Bool) (epsilon alpha kappa theta gamma : ℝ)
    (Vprime : ℝ → ℝ → ℝ)
    (u : ℝ → ℝ → Jet 1)
    (time1 accel2 grad1 lap2 : ℝ → ℝ → ℝ)
    (t x : ℝ) : ℝ :=
  force side epsilon alpha kappa theta gamma
      (Vprime t x) (u t x) -
    time1 t x + accel2 t x - grad1 t x + lap2 t x

/-- **Actual corrected S004 strong Euler operator separates under
all integrable test-field pairings**. E is not assumed zero; the
fundamental-lemma direction follows from the verified L² quadratic
nondegeneracy for each real component.

The residual coefficients must be the ACTUAL derivatives of the
nonlinear S004 momenta for this to represent the spacetime PDE.
Those derivative and trace hypotheses are supplied by the existing
`weakComponent_eq_strongComponent` theorem. Connecting its
admissible compact temporal test space by density is outstanding. -/
theorem corrected_euler_all_probes_iff_ae_equations
    (mu : Measure (ℝ × ℝ))
    (epsilon alpha kappa theta gamma : ℝ)
    (Vprime : ℝ → ℝ → ℝ)
    (u : ℝ → ℝ → Jet 1)
    (timeR1 accelR2 gradR1 lapR2 : ℝ → ℝ → ℝ)
    (timeI1 accelI2 gradI1 lapI2 : ℝ → ℝ → ℝ)
    (hR2 : Integrable
      (fun z => correctedEulerResidual true epsilon alpha kappa
        theta gamma Vprime u timeR1 accelR2 gradR1 lapR2 z.1 z.2 ^ 2) mu)
    (hI2 : Integrable
      (fun z => correctedEulerResidual false epsilon alpha kappa
        theta gamma Vprime u timeI1 accelI2 gradI1 lapI2 z.1 z.2 ^ 2) mu) :
    (∀ hR hI : ℝ × ℝ → ℝ,
      Integrable (fun z =>
        correctedEulerResidual true epsilon alpha kappa theta gamma
          Vprime u timeR1 accelR2 gradR1 lapR2 z.1 z.2 * hR z) mu →
      Integrable (fun z =>
        correctedEulerResidual false epsilon alpha kappa theta gamma
          Vprime u timeI1 accelI2 gradI1 lapI2 z.1 z.2 * hI z) mu →
      (∫ z,
        correctedEulerResidual true epsilon alpha kappa theta gamma
          Vprime u timeR1 accelR2 gradR1 lapR2 z.1 z.2 * hR z ∂mu) +
      (∫ z,
        correctedEulerResidual false epsilon alpha kappa theta gamma
          Vprime u timeI1 accelI2 gradI1 lapI2 z.1 z.2 * hI z ∂mu) = 0) ↔
    (∀ᵐ z ∂mu,
      correctedEulerResidual true epsilon alpha kappa theta gamma
        Vprime u timeR1 accelR2 gradR1 lapR2 z.1 z.2 = 0) ∧
    (∀ᵐ z ∂mu,
      correctedEulerResidual false epsilon alpha kappa theta gamma
        Vprime u timeI1 accelI2 gradI1 lapI2 z.1 z.2 = 0) := by
  exact two_component_integrable_probes_iff_ae_zero mu
    (fun z => correctedEulerResidual true epsilon alpha kappa
      theta gamma Vprime u timeR1 accelR2 gradR1 lapR2 z.1 z.2)
    (fun z => correctedEulerResidual false epsilon alpha kappa
      theta gamma Vprime u timeI1 accelI2 gradI1 lapI2 z.1 z.2)
    hR2 hI2

end WCTLean.S004EulerSeparation
