/-
  WCTLean/Models/FisherCurvature.lean

  E78 (issue #23): the curvature–Fisher relation

      I_F[ψ] ≥ c ∫ |Θ[ψ]|² dx                                   (E78)

  on the periodic one-dimensional model `[0, 2π]`, for the *maintained*
  corrected complex curvature operator `thetaComplex` (M2/E17/M6B) with the
  Laplacian realised as the second derivative.

  Results (periodic 1D model only; not whole-space WCT):

  * **Refutation of the universal form.**  For every regulator `ε` (any
    real number, including `ε = 0`), every `α ≥ 0` and every constant `c > 0`
    there is a smooth, `2π`-periodic field with `|ψ|² ≥ 1/4` violating E78
    (`e78_no_universal_constant`, `e78_universal_bound_false`).  The witness
    family `ψ_k = 1 + cos (k x) / 2` has `I_F = k² π` while the curvature
    energy is at least `k⁴ π / (9 + 4 ε²)²`.
  * **Corrected relation (exact identity).**  For a real `C²` field with
    `ψ ≠ 0` and periodic boundary values of `ψ, ψ'`, for *every* regulator
    `(ε, α)`:
        `I_F[ψ²] = 4 ∫ Re Θ_ε[ψ] · D_ε(ψ) dx = 4 ∫ (ψ')² dx`
    (`e78_fisher_curvature_identity`), where `D_ε` is the maintained
    corrected denominator.
  * **Corrected inequality (reverse direction).**  By Cauchy–Schwarz,
        `I_F[ψ²]² ≤ 16 (∫ D_ε²) (∫ |Θ_ε[ψ]|²)`
    (`e78_fisher_sq_le_curvature_energy`): Fisher information is *bounded by*
    the curvature energy, not the other way round.

  Assumptions are explicit hypotheses: positivity (`ψ x ≠ 0`),
  differentiability (`HasDerivAt` for `ψ` and `ψ'`, continuity of `ψ''`),
  periodic boundary values; integrability is derived from continuity.
-/

import Mathlib
import WCTLean.Fourier
import WCTLean.Models.ComplexCurvature

namespace WCTLean

open Real intervalIntegral
open scoped ContDiff

noncomputable section

/-! ### Definitions -/

/-- One-period Fisher information `∫₀^{2π} (ρ')² / ρ` of a density `ρ`. -/
def periodFisherInformation (ρ : ℝ → ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..(2 * π), deriv ρ x ^ 2 / ρ x

/-- The maintained corrected curvature field of a complex field on the
one-dimensional periodic model (`Δψ = ψ''`). -/
def curvatureField (ψ : ℝ → ℂ) (ε α : ℝ) (x : ℝ) : ℂ :=
  thetaComplex (deriv (deriv ψ) x) (ψ x) ε α

/-- One-period curvature energy `∫₀^{2π} |Θ_ε[ψ]|²`. -/
def periodCurvatureEnergy (ψ : ℝ → ℂ) (ε α : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..(2 * π), ‖curvatureField ψ ε α x‖ ^ 2

/-- The E78 inequality `c ∫ |Θ_ε[ψ]|² ≤ I_F[|ψ|²]` for one field. -/
def E78FisherBound (c ε α : ℝ) (ψ : ℝ → ℂ) : Prop :=
  c * periodCurvatureEnergy ψ ε α ≤ periodFisherInformation (fun x => Complex.normSq (ψ x))

/-- A real field viewed as a complex field. -/
def realField (ψ : ℝ → ℝ) : ℝ → ℂ :=
  fun x => (ψ x : ℂ)

/-! ### Elementary facts about the regularized operator on real fields -/

/-- On a real field value, the corrected denominator is `p² + ε² e^{-2αp²}`. -/
theorem complexRegularizerDenominator_ofReal (p ε α : ℝ) :
    complexRegularizerDenominator (p : ℂ) ε α = p * p + ε ^ 2 * Real.exp (-2 * α * (p * p)) := by
  simp [complexRegularizerDenominator, Complex.normSq_ofReal]

/-- On real inputs the maintained operator is real:
`Θ_ε = -(l p) / D_ε(p)`. -/
theorem thetaComplex_ofReal (l p ε α : ℝ) :
    thetaComplex (l : ℂ) (p : ℂ) ε α =
      ((-(l * p) / complexRegularizerDenominator (p : ℂ) ε α : ℝ) : ℂ) := by
  unfold thetaComplex complexRegularizedReciprocal
  have hstar : star (p : ℂ) = (p : ℂ) := Complex.conj_ofReal p
  rw [hstar]
  push_cast
  ring

/-- For a nonzero real field value the corrected denominator is positive for
every regulator. -/
theorem complexRegularizerDenominator_ofReal_pos (p ε α : ℝ) (hp : p ≠ 0) :
    0 < complexRegularizerDenominator (p : ℂ) ε α := by
  rw [complexRegularizerDenominator_ofReal]
  have h1 : 0 < p * p := mul_self_pos.mpr hp
  have h2 : 0 ≤ ε ^ 2 * Real.exp (-2 * α * (p * p)) :=
    mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  linarith

/-- `Θ_ε · D_ε = -(l p)` exactly, whenever `D_ε ≠ 0`. -/
theorem thetaComplex_ofReal_re_mul_denominator (l p ε α : ℝ)
    (hD : complexRegularizerDenominator (p : ℂ) ε α ≠ 0) :
    (thetaComplex (l : ℂ) (p : ℂ) ε α).re * complexRegularizerDenominator (p : ℂ) ε α =
      -(l * p) := by
  rw [thetaComplex_ofReal, Complex.ofReal_re]
  field_simp

/-! ### The witness family `ψ_k = 1 + cos (k x) / 2` -/

/-- Witness profile `1 + cos (k x) / 2`. -/
def e78Probe (k : ℕ) (x : ℝ) : ℝ :=
  1 + Real.cos (k * x) / 2

/-- The witness as a complex field. -/
def e78ProbeField (k : ℕ) : ℝ → ℂ :=
  realField (e78Probe k)

theorem e78Probe_hasDerivAt (k : ℕ) (x : ℝ) :
    HasDerivAt (e78Probe k) (-(k : ℝ) / 2 * Real.sin (k * x)) x := by
  have h1 : HasDerivAt (fun x : ℝ => (k : ℝ) * x) (k : ℝ) x := by
    simpa using (hasDerivAt_id x).const_mul (k : ℝ)
  have h2 := ((Real.hasDerivAt_cos ((k : ℝ) * x)).comp x h1).div_const 2 |>.const_add 1
  have hf : e78Probe k = fun x => 1 + (Real.cos ∘ fun x : ℝ => (k : ℝ) * x) x / 2 := by
    funext y; rfl
  rw [hf]
  convert h2 using 1
  ring

theorem e78Probe_deriv_hasDerivAt (k : ℕ) (x : ℝ) :
    HasDerivAt (fun x : ℝ => -(k : ℝ) / 2 * Real.sin (k * x))
      (-(k : ℝ) ^ 2 / 2 * Real.cos (k * x)) x := by
  have h1 : HasDerivAt (fun x : ℝ => (k : ℝ) * x) (k : ℝ) x := by
    simpa using (hasDerivAt_id x).const_mul (k : ℝ)
  have h2 := ((Real.hasDerivAt_sin ((k : ℝ) * x)).comp x h1).const_mul (-(k : ℝ) / 2)
  convert h2 using 1
  ring

theorem e78Probe_ge (k : ℕ) (x : ℝ) : 1 / 2 ≤ e78Probe k x := by
  unfold e78Probe
  linarith [Real.neg_one_le_cos ((k : ℝ) * x)]

theorem e78Probe_le (k : ℕ) (x : ℝ) : e78Probe k x ≤ 3 / 2 := by
  unfold e78Probe
  linarith [Real.cos_le_one ((k : ℝ) * x)]

theorem e78Probe_ne_zero (k : ℕ) (x : ℝ) : e78Probe k x ≠ 0 := by
  have := e78Probe_ge k x
  intro h; rw [h] at this; norm_num at this

theorem e78Probe_periodic (k : ℕ) : Function.Periodic (e78Probe k) (2 * π) := by
  intro x
  unfold e78Probe
  rw [show (k : ℝ) * (x + 2 * π) = (k : ℝ) * x + (k : ℝ) * (2 * π) by ring,
    Real.cos_add_nat_mul_two_pi]

theorem e78Probe_contDiff (k : ℕ) : ContDiff ℝ ∞ (e78Probe k) := by
  unfold e78Probe
  exact contDiff_const.add
    ((Real.contDiff_cos.comp (contDiff_const.mul contDiff_id)).div_const 2)

theorem e78ProbeField_contDiff (k : ℕ) : ContDiff ℝ ∞ (e78ProbeField k) :=
  Complex.ofRealCLM.contDiff.comp (e78Probe_contDiff k)

theorem e78ProbeField_periodic (k : ℕ) : Function.Periodic (e78ProbeField k) (2 * π) := by
  intro x
  simp only [e78ProbeField, realField, e78Probe_periodic k x]

theorem e78ProbeField_normSq (k : ℕ) (x : ℝ) :
    Complex.normSq (e78ProbeField k x) = e78Probe k x * e78Probe k x := by
  simp [e78ProbeField, realField, Complex.normSq_ofReal]

theorem e78ProbeField_normSq_ge (k : ℕ) (x : ℝ) :
    1 / 4 ≤ Complex.normSq (e78ProbeField k x) := by
  rw [e78ProbeField_normSq]
  have := e78Probe_ge k x
  nlinarith

theorem e78ProbeField_deriv (k : ℕ) :
    deriv (e78ProbeField k) = fun x => ((-(k : ℝ) / 2 * Real.sin (k * x) : ℝ) : ℂ) := by
  funext x
  exact (e78Probe_hasDerivAt k x).ofReal_comp.deriv

theorem e78ProbeField_deriv2 (k : ℕ) :
    deriv (deriv (e78ProbeField k)) =
      fun x => ((-(k : ℝ) ^ 2 / 2 * Real.cos (k * x) : ℝ) : ℂ) := by
  rw [e78ProbeField_deriv]
  funext x
  exact (e78Probe_deriv_hasDerivAt k x).ofReal_comp.deriv

/-- Exact Fisher information of the witness: `I_F[ψ_k²] = k² π`. -/
theorem e78Probe_fisher (k : ℕ) (hk : k ≠ 0) :
    periodFisherInformation (fun x => Complex.normSq (e78ProbeField k x)) = (k : ℝ) ^ 2 * π := by
  have hρ : (fun x => Complex.normSq (e78ProbeField k x)) =
      fun x => e78Probe k x * e78Probe k x := by
    funext x; exact e78ProbeField_normSq k x
  have hderiv : ∀ x, deriv (fun x => e78Probe k x * e78Probe k x) x =
      -(k : ℝ) / 2 * Real.sin (k * x) * e78Probe k x +
        e78Probe k x * (-(k : ℝ) / 2 * Real.sin (k * x)) := by
    intro x
    exact ((e78Probe_hasDerivAt k x).mul (e78Probe_hasDerivAt k x)).deriv
  have hpt : ∀ x : ℝ, deriv (fun x => e78Probe k x * e78Probe k x) x ^ 2 /
      (e78Probe k x * e78Probe k x) = (k : ℝ) ^ 2 * Real.sin (((k : ℤ) : ℝ) * x) ^ 2 := by
    intro x
    rw [hderiv x]
    have hp := e78Probe_ne_zero k x
    have hcast : (((k : ℤ) : ℝ)) = (k : ℝ) := Int.cast_natCast k
    rw [hcast]
    field_simp
    ring
  unfold periodFisherInformation
  rw [hρ]
  simp_rw [hpt]
  rw [intervalIntegral.integral_const_mul,
    integral_sin_sq_int_mul (n := (k : ℤ)) (by exact_mod_cast hk)]

/-- The witness family has `k`-independent mass `∫₀^{2π} ψ_k² = 9π/4` (`k ≠ 0`),
so the failure of E78 below is not a normalization artifact: normalizing the
density `ψ_k²` divides `I_F` by the same fixed constant for every `k`. -/
theorem e78Probe_mass (k : ℕ) (hk : k ≠ 0) :
    ∫ x in (0 : ℝ)..(2 * π), e78Probe k x ^ 2 = 9 * π / 4 := by
  have hk' : (k : ℤ) ≠ 0 := by exact_mod_cast hk
  have hcast : (((k : ℤ) : ℝ)) = (k : ℝ) := Int.cast_natCast k
  have hpt : ∀ x : ℝ, e78Probe k x ^ 2 =
      1 + Real.cos (((k : ℤ) : ℝ) * x) + (1 / 4) * Real.cos (((k : ℤ) : ℝ) * x) ^ 2 := by
    intro x; rw [hcast]; unfold e78Probe; ring
  simp_rw [hpt]
  have i1 : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) MeasureTheory.volume 0 (2 * π) :=
    intervalIntegral.intervalIntegrable_const
  have i2 : IntervalIntegrable (fun x : ℝ => Real.cos (((k : ℤ) : ℝ) * x))
      MeasureTheory.volume 0 (2 * π) := (Continuous.intervalIntegrable (by fun_prop) _ _)
  have i3 : IntervalIntegrable (fun x : ℝ => (1 / 4) * Real.cos (((k : ℤ) : ℝ) * x) ^ 2)
      MeasureTheory.volume 0 (2 * π) := (Continuous.intervalIntegrable (by fun_prop) _ _)
  rw [intervalIntegral.integral_add (i1.add i2) i3, intervalIntegral.integral_add i1 i2,
    intervalIntegral.integral_const_mul, integral_cos_int_mul_period hk',
    integral_cos_sq_int_mul hk']
  simp
  ring

/-- Regularized denominator along the witness. -/
def e78ProbeDenominator (k : ℕ) (ε α : ℝ) (x : ℝ) : ℝ :=
  e78Probe k x * e78Probe k x + ε ^ 2 * Real.exp (-2 * α * (e78Probe k x * e78Probe k x))

theorem e78ProbeDenominator_pos (k : ℕ) (ε α x : ℝ) : 0 < e78ProbeDenominator k ε α x := by
  have := complexRegularizerDenominator_ofReal_pos (e78Probe k x) ε α (e78Probe_ne_zero k x)
  rwa [complexRegularizerDenominator_ofReal] at this

theorem e78ProbeDenominator_le (k : ℕ) (ε α x : ℝ) (hα : 0 ≤ α) :
    e78ProbeDenominator k ε α x ≤ 9 / 4 + ε ^ 2 := by
  unfold e78ProbeDenominator
  have hp0 := e78Probe_ge k x
  have hp1 := e78Probe_le k x
  have hpp : e78Probe k x * e78Probe k x ≤ 9 / 4 := by nlinarith
  have hexp : Real.exp (-2 * α * (e78Probe k x * e78Probe k x)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have : 0 ≤ α * (e78Probe k x * e78Probe k x) := mul_nonneg hα (by nlinarith)
    linarith
  have : ε ^ 2 * Real.exp (-2 * α * (e78Probe k x * e78Probe k x)) ≤ ε ^ 2 :=
    mul_le_of_le_one_right (sq_nonneg ε) hexp
  linarith

theorem e78ProbeDenominator_continuous (k : ℕ) (ε α : ℝ) :
    Continuous (e78ProbeDenominator k ε α) := by
  have hp : Continuous (e78Probe k) := (e78Probe_contDiff k).continuous
  unfold e78ProbeDenominator
  fun_prop

/-- Real closed form of the maintained curvature field along the witness. -/
theorem e78Probe_curvatureField (k : ℕ) (ε α x : ℝ) :
    curvatureField (e78ProbeField k) ε α x =
      (((k : ℝ) ^ 2 / 2 * Real.cos (k * x) * e78Probe k x / e78ProbeDenominator k ε α x : ℝ)
        : ℂ) := by
  unfold curvatureField
  rw [e78ProbeField_deriv2]
  simp only [e78ProbeField, realField]
  rw [thetaComplex_ofReal, complexRegularizerDenominator_ofReal]
  unfold e78ProbeDenominator
  congr 1
  ring

/-- Pointwise lower bound for the witness curvature density. -/
theorem e78Probe_curvature_sq_ge (k : ℕ) (ε α x : ℝ) (hα : 0 ≤ α) :
    (k : ℝ) ^ 4 / (9 + 4 * ε ^ 2) ^ 2 * Real.cos (((k : ℤ) : ℝ) * x) ^ 2 ≤
      ‖curvatureField (e78ProbeField k) ε α x‖ ^ 2 := by
  rw [e78Probe_curvatureField, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hcast : (((k : ℤ) : ℝ)) = (k : ℝ) := Int.cast_natCast k
  rw [hcast]
  set p := e78Probe k x with hp_def
  set D := e78ProbeDenominator k ε α x with hD_def
  set C := Real.cos ((k : ℝ) * x) with hC_def
  have hD : 0 < D := e78ProbeDenominator_pos k ε α x
  have hDle : D ≤ 9 / 4 + ε ^ 2 := e78ProbeDenominator_le k ε α x hα
  have hp : 1 / 2 ≤ p := e78Probe_ge k x
  have hE : 0 < 9 + 4 * ε ^ 2 := by positivity
  -- `p / D ≥ 2 / (9 + 4 ε²)`
  have hratio : 2 / (9 + 4 * ε ^ 2) ≤ p / D := by
    rw [div_le_div_iff₀ hE hD]
    nlinarith
  have hratio0 : 0 ≤ 2 / (9 + 4 * ε ^ 2) := by positivity
  have hsq : (2 / (9 + 4 * ε ^ 2)) ^ 2 ≤ (p / D) ^ 2 :=
    pow_le_pow_left₀ hratio0 hratio 2
  have hrewrite : ((k : ℝ) ^ 2 / 2 * C * p / D) ^ 2 =
      ((k : ℝ) ^ 4 / 4 * C ^ 2) * (p / D) ^ 2 := by
    field_simp
    ring
  have hlower : (k : ℝ) ^ 4 / (9 + 4 * ε ^ 2) ^ 2 * C ^ 2 =
      ((k : ℝ) ^ 4 / 4 * C ^ 2) * (2 / (9 + 4 * ε ^ 2)) ^ 2 := by
    field_simp
    ring
  rw [hrewrite, hlower]
  exact mul_le_mul_of_nonneg_left hsq (by positivity)

theorem e78Probe_curvature_sq_continuous (k : ℕ) (ε α : ℝ) :
    Continuous fun x => ‖curvatureField (e78ProbeField k) ε α x‖ ^ 2 := by
  have hp : Continuous (e78Probe k) := (e78Probe_contDiff k).continuous
  have hD := e78ProbeDenominator_continuous k ε α
  have hfun : (fun x => ‖curvatureField (e78ProbeField k) ε α x‖ ^ 2) =
      fun x => ‖((((k : ℝ) ^ 2 / 2 * Real.cos (k * x) * e78Probe k x /
        e78ProbeDenominator k ε α x : ℝ)) : ℂ)‖ ^ 2 := by
    funext x; rw [e78Probe_curvatureField]
  rw [hfun]
  have hq : Continuous fun x => (k : ℝ) ^ 2 / 2 * Real.cos (k * x) * e78Probe k x /
      e78ProbeDenominator k ε α x :=
    Continuous.div (by fun_prop) hD fun x => ne_of_gt (e78ProbeDenominator_pos k ε α x)
  exact (Complex.continuous_ofReal.comp hq).norm.pow 2

/-- Lower bound on the curvature energy of the witness:
`∫ |Θ_ε[ψ_k]|² ≥ k⁴ π / (9 + 4 ε²)²`. -/
theorem e78Probe_curvatureEnergy_ge (k : ℕ) (hk : k ≠ 0) (ε α : ℝ) (hα : 0 ≤ α) :
    (k : ℝ) ^ 4 * π / (9 + 4 * ε ^ 2) ^ 2 ≤ periodCurvatureEnergy (e78ProbeField k) ε α := by
  unfold periodCurvatureEnergy
  have hlow : ∫ x in (0 : ℝ)..(2 * π),
      (k : ℝ) ^ 4 / (9 + 4 * ε ^ 2) ^ 2 * Real.cos (((k : ℤ) : ℝ) * x) ^ 2 =
        (k : ℝ) ^ 4 * π / (9 + 4 * ε ^ 2) ^ 2 := by
    rw [intervalIntegral.integral_const_mul,
      integral_cos_sq_int_mul (n := (k : ℤ)) (by exact_mod_cast hk)]
    ring
  rw [← hlow]
  apply intervalIntegral.integral_mono_on (by positivity)
  · exact (Continuous.intervalIntegrable (by fun_prop) _ _)
  · exact (e78Probe_curvature_sq_continuous k ε α).intervalIntegrable _ _
  · intro x _
    exact e78Probe_curvature_sq_ge k ε α x hα

/-! ### Refutation of the universal E78 inequality -/

/-- For each nonzero mode number the witness has Fisher information `k² π`
and curvature energy at least `k⁴ π / (9 + 4 ε²)²`. -/
theorem e78Probe_fisher_and_energy (k : ℕ) (hk : k ≠ 0) (ε α : ℝ) (hα : 0 ≤ α) :
    periodFisherInformation (fun x => Complex.normSq (e78ProbeField k x)) = (k : ℝ) ^ 2 * π ∧
      (k : ℝ) ^ 4 * π / (9 + 4 * ε ^ 2) ^ 2 ≤ periodCurvatureEnergy (e78ProbeField k) ε α :=
  ⟨e78Probe_fisher k hk, e78Probe_curvatureEnergy_ge k hk ε α hα⟩

/-- **E78 has no universal constant.**  For every regulator `ε`, every
`α ≥ 0` and every `c > 0`, some smooth periodic witness `ψ_k` violates
`c ∫ |Θ_ε[ψ_k]|² ≤ I_F[|ψ_k|²]`. -/
theorem e78_no_universal_constant (c ε α : ℝ) (hc : 0 < c) (hα : 0 ≤ α) :
    ∃ k : ℕ, k ≠ 0 ∧ ¬ E78FisherBound c ε α (e78ProbeField k) := by
  set E := (9 + 4 * ε ^ 2) ^ 2 with hE_def
  have hE : 0 < E := by positivity
  obtain ⟨n, hn⟩ := exists_nat_gt (E / c)
  refine ⟨n + 1, Nat.succ_ne_zero n, ?_⟩
  intro hbound
  unfold E78FisherBound at hbound
  have hk : (n + 1 : ℕ) ≠ 0 := Nat.succ_ne_zero n
  rw [e78Probe_fisher (n + 1) hk] at hbound
  have henergy := e78Probe_curvatureEnergy_ge (n + 1) hk ε α hα
  set K : ℝ := ((n + 1 : ℕ) : ℝ) with hK_def
  have hK1 : 1 ≤ K := by rw [hK_def]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hKpos : 0 < K := by linarith
  -- `c K² > E`
  have hcK : E < c * K ^ 2 := by
    have h1 : E / c < K := by
      have : (n : ℝ) < K := by rw [hK_def]; push_cast; linarith
      linarith
    have h2 : K ≤ K ^ 2 := by nlinarith
    have h3 : E < c * K := by
      rw [div_lt_iff₀ hc] at h1; linarith
    nlinarith
  -- `c * energy ≥ c K⁴ π / E > K² π`
  have hlow : c * (K ^ 4 * π / E) ≤ c * periodCurvatureEnergy (e78ProbeField (n + 1)) ε α :=
    mul_le_mul_of_nonneg_left henergy hc.le
  have hstrict : K ^ 2 * π < c * (K ^ 4 * π / E) := by
    rw [mul_div_assoc', lt_div_iff₀ hE]
    have hpi := Real.pi_pos
    have hK2 : 0 < K ^ 2 := by positivity
    have : K ^ 2 * π * E < K ^ 2 * π * (c * K ^ 2) :=
      mul_lt_mul_of_pos_left hcK (by positivity)
    nlinarith
  linarith

/-- **E78 is false as a universal inequality** on smooth periodic fields with
`|ψ|² ≥ 1/4`, for every fixed regulator `ε` and every `α ≥ 0`. -/
theorem e78_universal_bound_false (ε α : ℝ) (hα : 0 ≤ α) :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ ψ : ℝ → ℂ, ContDiff ℝ ∞ ψ → Function.Periodic ψ (2 * π) →
      (∀ x, 1 / 4 ≤ Complex.normSq (ψ x)) → E78FisherBound c ε α ψ := by
  rintro ⟨c, hc, hall⟩
  obtain ⟨k, _, hk⟩ := e78_no_universal_constant c ε α hc hα
  exact hk (hall _ (e78ProbeField_contDiff k) (e78ProbeField_periodic k)
    (e78ProbeField_normSq_ge k))

/-! ### The corrected curvature–Fisher relation for real periodic fields -/

/-- Periodic integration by parts: `∫₀^{2π} ψ ψ'' = -∫₀^{2π} (ψ')²`. -/
theorem periodic_integral_mul_second_deriv (ψ ψ' ψ'' : ℝ → ℝ)
    (h1 : ∀ x, HasDerivAt ψ (ψ' x) x) (h2 : ∀ x, HasDerivAt ψ' (ψ'' x) x)
    (hc : Continuous ψ'') (hp0 : ψ (2 * π) = ψ 0) (hp1 : ψ' (2 * π) = ψ' 0) :
    ∫ x in (0 : ℝ)..(2 * π), ψ x * ψ'' x = -∫ x in (0 : ℝ)..(2 * π), ψ' x ^ 2 := by
  have hc' : Continuous ψ' := continuous_iff_continuousAt.2 fun x => (h2 x).continuousAt
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := 2 * π)
    (u := ψ) (v := ψ') (u' := ψ') (v' := ψ'') (fun x _ => h1 x) (fun x _ => h2 x)
    (hc'.intervalIntegrable _ _) (hc.intervalIntegrable _ _)
  rw [h, hp0, hp1, sub_self, zero_sub]
  simp only [sq]

/-- Fisher information of `ψ²` for a nonvanishing differentiable real field:
`I_F[ψ²] = 4 ∫ (ψ')²`. -/
theorem fisher_sq_eq_four_dirichlet (ψ ψ' : ℝ → ℝ) (h1 : ∀ x, HasDerivAt ψ (ψ' x) x)
    (hne : ∀ x, ψ x ≠ 0) :
    periodFisherInformation (fun x => ψ x * ψ x) = 4 * ∫ x in (0 : ℝ)..(2 * π), ψ' x ^ 2 := by
  have hpt : ∀ x, deriv (fun x => ψ x * ψ x) x ^ 2 / (ψ x * ψ x) = 4 * ψ' x ^ 2 := by
    intro x
    have hd : HasDerivAt (fun y => ψ y * ψ y) (ψ' x * ψ x + ψ x * ψ' x) x := (h1 x).mul (h1 x)
    rw [hd.deriv]
    have := hne x
    field_simp
    ring
  unfold periodFisherInformation
  simp_rw [hpt]
  rw [intervalIntegral.integral_const_mul]

/-- Second derivative of a complexified real `C²` field. -/
theorem realField_deriv2 (ψ ψ' ψ'' : ℝ → ℝ)
    (h1 : ∀ x, HasDerivAt ψ (ψ' x) x) (h2 : ∀ x, HasDerivAt ψ' (ψ'' x) x) :
    deriv (deriv (realField ψ)) = fun x => (ψ'' x : ℂ) := by
  have hd : deriv (realField ψ) = fun x => (ψ' x : ℂ) := by
    funext x; exact (h1 x).ofReal_comp.deriv
  rw [hd]
  funext x
  exact (h2 x).ofReal_comp.deriv

/-- The maintained curvature field of a complexified real field. -/
theorem realField_curvatureField (ψ ψ' ψ'' : ℝ → ℝ)
    (h1 : ∀ x, HasDerivAt ψ (ψ' x) x) (h2 : ∀ x, HasDerivAt ψ' (ψ'' x) x) (ε α x : ℝ) :
    curvatureField (realField ψ) ε α x = thetaComplex (ψ'' x : ℂ) (ψ x : ℂ) ε α := by
  unfold curvatureField
  rw [realField_deriv2 ψ ψ' ψ'' h1 h2]
  rfl

/-- **Corrected E78 identity.**  For a real `C²` field with no zeros and
periodic boundary values of `ψ` and `ψ'`, for *every* regulator `(ε, α)`:
`I_F[|ψ|²] = 4 ∫ Re Θ_ε[ψ] · D_ε(ψ) = 4 ∫ (ψ')²`. -/
theorem e78_fisher_curvature_identity (ψ ψ' ψ'' : ℝ → ℝ)
    (h1 : ∀ x, HasDerivAt ψ (ψ' x) x) (h2 : ∀ x, HasDerivAt ψ' (ψ'' x) x)
    (hc : Continuous ψ'') (hne : ∀ x, ψ x ≠ 0)
    (hp0 : ψ (2 * π) = ψ 0) (hp1 : ψ' (2 * π) = ψ' 0) (ε α : ℝ) :
    periodFisherInformation (fun x => Complex.normSq (realField ψ x)) =
        4 * ∫ x in (0 : ℝ)..(2 * π),
          (curvatureField (realField ψ) ε α x).re *
            complexRegularizerDenominator (realField ψ x) ε α ∧
      periodFisherInformation (fun x => Complex.normSq (realField ψ x)) =
        4 * ∫ x in (0 : ℝ)..(2 * π), ψ' x ^ 2 := by
  have hρ : (fun x => Complex.normSq (realField ψ x)) = fun x => ψ x * ψ x := by
    funext x; simp [realField, Complex.normSq_ofReal]
  have hfisher : periodFisherInformation (fun x => Complex.normSq (realField ψ x)) =
      4 * ∫ x in (0 : ℝ)..(2 * π), ψ' x ^ 2 := by
    rw [hρ]; exact fisher_sq_eq_four_dirichlet ψ ψ' h1 hne
  refine ⟨?_, hfisher⟩
  have hpt : ∀ x, (curvatureField (realField ψ) ε α x).re *
      complexRegularizerDenominator (realField ψ x) ε α = -(ψ x * ψ'' x) := by
    intro x
    rw [realField_curvatureField ψ ψ' ψ'' h1 h2]
    simp only [realField]
    rw [thetaComplex_ofReal_re_mul_denominator _ _ _ _
      (ne_of_gt (complexRegularizerDenominator_ofReal_pos _ ε α (hne x)))]
    ring
  simp_rw [hpt]
  rw [intervalIntegral.integral_neg,
    periodic_integral_mul_second_deriv ψ ψ' ψ'' h1 h2 hc hp0 hp1, neg_neg, hfisher]

/-! ### Cauchy–Schwarz and the reverse E78 inequality -/

/-- Cauchy–Schwarz for interval integrals of continuous real functions. -/
theorem interval_cauchy_schwarz {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    {a b : ℝ} (hab : a ≤ b) :
    (∫ x in a..b, f x * g x) ^ 2 ≤ (∫ x in a..b, f x ^ 2) * ∫ x in a..b, g x ^ 2 := by
  have hquad : ∀ t : ℝ, 0 ≤ (∫ x in a..b, g x ^ 2) * (t * t) +
      (2 * ∫ x in a..b, f x * g x) * t + ∫ x in a..b, f x ^ 2 := by
    intro t
    have hnonneg : 0 ≤ ∫ x in a..b, (f x + t * g x) ^ 2 :=
      intervalIntegral.integral_nonneg hab fun x _ => sq_nonneg _
    have hexpand : ∫ x in a..b, (f x + t * g x) ^ 2 =
        (∫ x in a..b, g x ^ 2) * (t * t) + (2 * ∫ x in a..b, f x * g x) * t +
          ∫ x in a..b, f x ^ 2 := by
      have hpt : ∀ x, (f x + t * g x) ^ 2 =
          (t * t) * g x ^ 2 + (2 * t) * (f x * g x) + f x ^ 2 := by
        intro x; ring
      simp_rw [hpt]
      have i1 : IntervalIntegrable (fun x => (t * t) * g x ^ 2) MeasureTheory.volume a b :=
        (Continuous.intervalIntegrable (by fun_prop) _ _)
      have i2 : IntervalIntegrable (fun x => (2 * t) * (f x * g x)) MeasureTheory.volume a b :=
        (Continuous.intervalIntegrable (by fun_prop) _ _)
      have i3 : IntervalIntegrable (fun x => f x ^ 2) MeasureTheory.volume a b :=
        (Continuous.intervalIntegrable (by fun_prop) _ _)
      rw [intervalIntegral.integral_add (i1.add i2) i3, intervalIntegral.integral_add i1 i2,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      ring
    rw [← hexpand]; exact hnonneg
  have hd := discrim_le_zero hquad
  unfold discrim at hd
  nlinarith

/-- **Reverse E78 inequality.**  For a real `C²` field with no zeros and
periodic boundary values, for every regulator `(ε, α)`:
`I_F[|ψ|²]² ≤ 16 (∫ D_ε²) (∫ |Θ_ε[ψ]|²)`. -/
theorem e78_fisher_sq_le_curvature_energy (ψ ψ' ψ'' : ℝ → ℝ)
    (h1 : ∀ x, HasDerivAt ψ (ψ' x) x) (h2 : ∀ x, HasDerivAt ψ' (ψ'' x) x)
    (hc : Continuous ψ'') (hne : ∀ x, ψ x ≠ 0)
    (hp0 : ψ (2 * π) = ψ 0) (hp1 : ψ' (2 * π) = ψ' 0) (ε α : ℝ) :
    periodFisherInformation (fun x => Complex.normSq (realField ψ x)) ^ 2 ≤
      16 * (∫ x in (0 : ℝ)..(2 * π), complexRegularizerDenominator (realField ψ x) ε α ^ 2) *
        periodCurvatureEnergy (realField ψ) ε α := by
  have hψc : Continuous ψ := continuous_iff_continuousAt.2 fun x => (h1 x).continuousAt
  -- explicit real forms
  set D : ℝ → ℝ := fun x => complexRegularizerDenominator (realField ψ x) ε α with hD_def
  have hDform : D = fun x => ψ x * ψ x + ε ^ 2 * Real.exp (-2 * α * (ψ x * ψ x)) := by
    funext x; simp only [hD_def, realField]; exact complexRegularizerDenominator_ofReal _ ε α
  have hDc : Continuous D := by rw [hDform]; fun_prop
  have hDpos : ∀ x, 0 < D x := fun x =>
    complexRegularizerDenominator_ofReal_pos (ψ x) ε α (hne x)
  set Θr : ℝ → ℝ := fun x => (curvatureField (realField ψ) ε α x).re with hΘr_def
  have hΘform : Θr = fun x => -(ψ'' x * ψ x) / D x := by
    funext x
    simp only [hΘr_def, hD_def]
    rw [realField_curvatureField ψ ψ' ψ'' h1 h2, thetaComplex_ofReal, Complex.ofReal_re]
    rfl
  have hΘc : Continuous Θr := by
    rw [hΘform]
    exact Continuous.div (by fun_prop) hDc fun x => ne_of_gt (hDpos x)
  have hnorm : ∀ x, ‖curvatureField (realField ψ) ε α x‖ ^ 2 = Θr x ^ 2 := by
    intro x
    simp only [hΘr_def]
    rw [realField_curvatureField ψ ψ' ψ'' h1 h2, thetaComplex_ofReal, Complex.norm_real,
      Complex.ofReal_re, Real.norm_eq_abs, sq_abs]
  obtain ⟨hid, _⟩ := e78_fisher_curvature_identity ψ ψ' ψ'' h1 h2 hc hne hp0 hp1 ε α
  have hcs := interval_cauchy_schwarz hΘc hDc (a := 0) (b := 2 * π) (by positivity)
  have henergy : periodCurvatureEnergy (realField ψ) ε α = ∫ x in (0 : ℝ)..(2 * π), Θr x ^ 2 := by
    unfold periodCurvatureEnergy
    simp_rw [hnorm]
  rw [hid, henergy]
  have : (4 * ∫ x in (0 : ℝ)..(2 * π), Θr x * D x) ^ 2 =
      16 * (∫ x in (0 : ℝ)..(2 * π), Θr x * D x) ^ 2 := by ring
  rw [this]
  have h16 : (0 : ℝ) ≤ 16 := by norm_num
  calc 16 * (∫ x in (0 : ℝ)..(2 * π), Θr x * D x) ^ 2
      ≤ 16 * ((∫ x in (0 : ℝ)..(2 * π), Θr x ^ 2) * ∫ x in (0 : ℝ)..(2 * π), D x ^ 2) :=
        mul_le_mul_of_nonneg_left hcs h16
    _ = 16 * (∫ x in (0 : ℝ)..(2 * π), D x ^ 2) * ∫ x in (0 : ℝ)..(2 * π), Θr x ^ 2 := by ring

end

end WCTLean
