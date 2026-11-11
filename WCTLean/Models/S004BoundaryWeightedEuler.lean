import Mathlib
import WCTLean.Models.S004ContinuousEuler

/-!
# Boundary-compatible weighted fundamental lemma on a real spacetime cell

For a finite open time interval (a,b) and open periodic spatial cell,
let w(t)=(t-a)^2(b-t)^2. It is strictly positive in the interior,
but w(a)=w(b)=w'(a)=w'(b)=0.

Instead of demanding a whole L² test-function density theorem, a
smooth S004 Euler residual E may be tested against h(t,x)=w(t)*E(t,x).
If this specific test is allowed by the original smooth periodic
variation class, stationarity forces E=0 a.e. on the spacetime
interior. This file proves the integral separation and the precise
abstract admissibility interface WITHOUT assuming E=0.

Still open: show the weighted residual is an admissible C²/Sobolev
S004 variation for the actual smooth background and traces, and
identify the action's first variation with its Euler pairing.
-/

open MeasureTheory Set

namespace WCTLean.S004BoundaryWeightedEuler

/-- The ordinary real Lebesgue measure on the OPEN spacetime rectangle.
Boundary endpoints have no role in the zero-integral argument. -/
noncomputable def interiorVolume
    (a b c d : ℝ) : Measure (ℝ × ℝ) :=
  (volume : Measure (ℝ × ℝ)).restrict (Ioo a b ×ˢ Ioo c d)

/-- Nonnegative polynomial weight vanishing quadratically at each
temporal endpoint. -/
def timeWeight (a b : ℝ) (z : ℝ × ℝ) : ℝ :=
  (z.1 - a) ^ 2 * (b - z.1) ^ 2

theorem timeWeight_nonneg (a b : ℝ) (z : ℝ × ℝ) :
    0 ≤ timeWeight a b z := by
  unfold timeWeight
  positivity

/-- Strict positivity in the spacetime INTERIOR, with no unproved
claim about endpoint traces or infinite-volume whole space. -/
theorem timeWeight_pos_of_mem
    (a b c d : ℝ) (z : ℝ × ℝ)
    (hz : z ∈ Ioo a b ×ˢ Ioo c d) :
    0 < timeWeight a b z := by
  rcases hz with ⟨⟨hta, htb⟩, _⟩
  unfold timeWeight
  exact mul_pos
    (sq_pos_of_pos (sub_pos.mpr hta))
    (sq_pos_of_pos (sub_pos.mpr htb))

/-- **Weighted integral fundamental lemma**, proved for the actual
restricted Lebesgue measure by testing the nonnegative function
E² w and using its a.e. zero criterion. It is NOT an axiom of
distributional separation. -/
theorem weighted_zero_integral_iff_ae_zero
    (a b c d : ℝ) (E : ℝ × ℝ → ℝ)
    (hInt : Integrable
      (fun z => E z ^ 2 * timeWeight a b z)
      (interiorVolume a b c d)) :
    (∫ z, E z ^ 2 * timeWeight a b z
      ∂interiorVolume a b c d) = 0 ↔
    (∀ᵐ z ∂interiorVolume a b c d, E z = 0) := by
  have hpos : ∀ z : ℝ × ℝ,
      0 ≤ E z ^ 2 * timeWeight a b z := by
    intro z
    exact mul_nonneg (sq_nonneg (E z)) (timeWeight_nonneg a b z)
  have hmem : ∀ᵐ z ∂interiorVolume a b c d,
      z ∈ Ioo a b ×ˢ Ioo c d := by
    exact MeasureTheory.ae_restrict_mem
      (measurableSet_Ioo.prod measurableSet_Ioo)
  constructor
  · intro hzero
    have hnonnegZero :=
      (MeasureTheory.integral_eq_zero_iff_of_nonneg hpos hInt).mp hzero
    filter_upwards [hnonnegZero, hmem] with z hz hinside
    have hz0 : E z ^ 2 * timeWeight a b z = 0 := by
      simpa using hz
    have hwpos : timeWeight a b z ≠ 0 :=
      ne_of_gt (timeWeight_pos_of_mem a b c d z hinside)
    have hE2 : E z ^ 2 = 0 :=
      (mul_eq_zero.mp hz0).resolve_right hwpos
    nlinarith [sq_nonneg (E z)]
  · intro hzero
    have hae : (fun z => E z ^ 2 * timeWeight a b z) =ᵐ[
        interiorVolume a b c d] (fun _ => (0 : ℝ)) := by
      filter_upwards [hzero] with z hz
      simp [hz]
    calc
      (∫ z, E z ^ 2 * timeWeight a b z
        ∂interiorVolume a b c d) =
        (∫ _z, (0 : ℝ) ∂interiorVolume a b c d) :=
        integral_congr_ae hae
      _ = 0 := by simp

/-- One boundary-compatible TEST SUFFICES, provided the independently
defined admissible-variation class actually CONTAINS it. Neither the
Euler equation nor the desired integral is hidden as a hypothesis.

The analytic admissibility proof, including its time derivatives and
periodic spatial traces, is a separate check on smooth S004 fields. -/
theorem zero_variation_on_boundary_test_forces_ae_euler
    (a b c d : ℝ)
    (E : ℝ × ℝ → ℝ)
    (Allowed : (ℝ × ℝ → ℝ) → Prop)
    (hAllowed :
      Allowed (fun z => E z * timeWeight a b z))
    (hInt : Integrable
      (fun z => E z ^ 2 * timeWeight a b z)
      (interiorVolume a b c d))
    (hCritical : ∀ h : ℝ × ℝ → ℝ,
      Allowed h →
      (∫ z, E z * h z ∂interiorVolume a b c d) = 0) :
    ∀ᵐ z ∂interiorVolume a b c d, E z = 0 := by
  have hzero := hCritical
    (fun z => E z * timeWeight a b z) hAllowed
  have hweighted :
      (∫ z, E z ^ 2 * timeWeight a b z
        ∂interiorVolume a b c d) = 0 := by
    simpa only [pow_two, mul_assoc] using hzero
  exact (weighted_zero_integral_iff_ae_zero a b c d E hInt).mp
    hweighted

/-! ## Admissible temporal traces of the explicit residual test -/

/-- The chosen polynomial weight has the exact time derivative
2(t-a)(b-t)²-2(b-t)(t-a)², proved by real differentiation. -/
theorem timeWeight_hasDerivAt
    (a b x t : ℝ) :
    HasDerivAt (fun s : ℝ => timeWeight a b (s,x))
      (2 * (t-a) * (b-t)^2 - 2*(b-t)*(t-a)^2) t := by
  have ha : HasDerivAt (fun s : ℝ => s-a) 1 t := by
    convert (hasDerivAt_id t).sub_const a using 1 <;> ring
  have hb : HasDerivAt (fun s : ℝ => b-s) (-1) t := by
    convert (hasDerivAt_id t).neg.const_add b using 1 <;> ring
  have hh := (ha.pow 2).mul (hb.pow 2)
  convert hh using 1 <;>
    (try funext s) <;>
    simp only [timeWeight] <;>
    ring

/-- Both the weight AND its first temporal derivative vanish
at BOTH time boundaries, precisely what is needed for the
second-order temporal Green identity in the corrected S004
Euler derivation. -/
theorem timeWeight_zero_endpoints
    (a b x : ℝ) :
    timeWeight a b (a,x) = 0 ∧
      timeWeight a b (b,x) = 0 ∧
      HasDerivAt (fun s : ℝ => timeWeight a b (s,x)) 0 a ∧
      HasDerivAt (fun s : ℝ => timeWeight a b (s,x)) 0 b := by
  refine ⟨by simp [timeWeight], by simp [timeWeight], ?_, ?_⟩
  · simpa using timeWeight_hasDerivAt a b x a
  · simpa using timeWeight_hasDerivAt a b x b

/-- If an Euler residual has ordinary first time derivatives at the
endpoints, the EXPLICIT test h=w(t) E(t,x) has both zero value and
zero first time derivative at both endpoints. This DISCHARGES
the temporal boundary assumptions for this one useful test, rather
than postulating its admissibility. -/
theorem weighted_test_zero_temporal_traces
    (a b x : ℝ) (E : ℝ → ℝ → ℝ)
    (hEa : DifferentiableAt ℝ (fun s => E s x) a)
    (hEb : DifferentiableAt ℝ (fun s => E s x) b) :
    E a x * timeWeight a b (a,x) = 0 ∧
    E b x * timeWeight a b (b,x) = 0 ∧
    HasDerivAt (fun s => E s x * timeWeight a b (s,x)) 0 a ∧
    HasDerivAt (fun s => E s x * timeWeight a b (s,x)) 0 b := by
  obtain ⟨hva, hvb, hda, hdb⟩ := timeWeight_zero_endpoints a b x
  refine ⟨by rw [hva]; ring, by rw [hvb]; ring, ?_, ?_⟩
  · have hh := hEa.hasDerivAt.mul hda
    simpa [hva] using hh
  · have hh := hEb.hasDerivAt.mul hdb
    simpa [hvb] using hh

/-- The same residual-weight test preserves the spatial PERIODIC
value trace whenever E itself is periodic. The weight depends
only on time, so no unproved spatial projection is needed. -/
theorem weighted_test_periodic_values
    (a b c d : ℝ) (E : ℝ → ℝ → ℝ)
    (hperiodic : ∀ t, E t c = E t d) :
    ∀ t, E t c * timeWeight a b (t,c) =
      E t d * timeWeight a b (t,d) := by
  intro t
  simp [timeWeight, hperiodic t]

/-! ## Concrete temporal-and-periodic test-function separation -/

/-- Explicit boundary-trace class for 1+1 smooth periodic variations.
Both the variation and its first temporal derivative vanish at
the time endpoints; its values agree across the spatial period.
No Euler-equation assumption is present in this definition.

The complete S004 second-order spatial Green theorem additionally
requires matching first spatial derivatives and regularity of the
test. Those are NOT silently included in this restricted predicate. -/
def BoundaryPeriodicTest (a b c d : ℝ)
    (h : ℝ → ℝ → ℝ) : Prop :=
  (∀ x,
    h a x = 0 ∧ h b x = 0 ∧
    HasDerivAt (fun t => h t x) 0 a ∧
    HasDerivAt (fun t => h t x) 0 b) ∧
  (∀ t, h t c = h t d)

/-- The explicit weighted residual test satisfies the ACTUAL temporal
endpoint conditions and value-level spatial periodicity, under only
ordinary temporal differentiability and periodicity of E.
Admissibility is DERIVED, not postulated as a convenient assumption. -/
theorem weighted_residual_is_boundary_periodic_test
    (a b c d : ℝ) (E : ℝ → ℝ → ℝ)
    (hEa : ∀ x, DifferentiableAt ℝ (fun t => E t x) a)
    (hEb : ∀ x, DifferentiableAt ℝ (fun t => E t x) b)
    (hPer : ∀ t, E t c = E t d) :
    BoundaryPeriodicTest a b c d
      (fun t x => E t x * timeWeight a b (t,x)) := by
  constructor
  · intro x
    exact weighted_test_zero_temporal_traces
      a b x E (hEa x) (hEb x)
  · exact weighted_test_periodic_values a b c d E hPer

/-- **Concrete boundary-periodic fundamental lemma** for a smooth
candidate Euler residual: if its pairing vanishes for every test
satisfying the specified ZERO temporal first-order traces and
matching spatial values, the Euler residual is zero almost
everywhere on the spacetime interior.

The proof constructs one specific nonnegative weighted-residual
variation, verifies all its stated trace conditions, and derives
E=0 from nonnegative Lebesgue integration. No L² test-density
assumption or abstract separation axiom is used.

To apply this directly to ORIGINAL S004 critical points, further
show that the actual C²/Sobolev variation class contains these
tests (including matching spatial derivative traces), and connect
the action derivative to the strong Euler integral. -/
theorem boundary_periodic_test_critical_forces_ae_euler
    (a b c d : ℝ) (E : ℝ → ℝ → ℝ)
    (hEa : ∀ x, DifferentiableAt ℝ (fun t => E t x) a)
    (hEb : ∀ x, DifferentiableAt ℝ (fun t => E t x) b)
    (hPer : ∀ t, E t c = E t d)
    (hInt : Integrable
      (fun z => E z.1 z.2 ^ 2 * timeWeight a b z)
      (interiorVolume a b c d))
    (hCritical : ∀ h : ℝ → ℝ → ℝ,
      BoundaryPeriodicTest a b c d h →
      (∫ z, E z.1 z.2 * h z.1 z.2
        ∂interiorVolume a b c d) = 0) :
    ∀ᵐ z ∂interiorVolume a b c d, E z.1 z.2 = 0 := by
  have hAllowed := weighted_residual_is_boundary_periodic_test
    a b c d E hEa hEb hPer
  have hzero := hCritical
    (fun t x => E t x * timeWeight a b (t,x)) hAllowed
  have hweightzero :
      (∫ z, E z.1 z.2 ^ 2 * timeWeight a b z
        ∂interiorVolume a b c d) = 0 := by
    simpa only [pow_two, mul_assoc] using hzero
  exact (weighted_zero_integral_iff_ae_zero a b c d
    (fun z => E z.1 z.2) hInt).mp hweightzero

end WCTLean.S004BoundaryWeightedEuler
