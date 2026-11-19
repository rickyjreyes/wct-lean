/-
  WCTLean/Models/M7LinearSemigroup.lean

  Issues #19 / #21: the *linear part* of the M7 evolution as a genuine
  evolution operator on the function space `L²(AddCircle T; ℂ)`.

  Every real Fourier symbol `σ : ℤ → ℝ` that is bounded above by `μ`
  (in particular the M7 linear symbol `c₁(σ₀² - k²) - c₂(k⋆² - k²)²` with
  `c₂ > 0`, and the M3/M7 Swift–Hohenberg symbol of `Models/BandPass.lean`)
  generates

      S(t) f = ∑ₙ e^{t σ(n)} f̂(n) e_n,    t ≥ 0.

  Proved (periodic one-dimensional model; linear equation only):

  * well-defined on all of `L²` (`evolution`, `fourierCoeff_evolution`);
  * semigroup law, identity at `t = 0`, linearity
    (`evolution_add_time`, `evolution_zero`, `evolution_sub`);
  * global bound `‖S(t)f‖ ≤ e^{μt}‖f‖` and Lipschitz dependence on data
    (`norm_evolution_le`, `norm_evolution_sub_le`);
  * strong continuity `S(t)f → f` as `t → 0` (`tendsto_evolution_zero`);
  * existence and uniqueness of Fourier-mild solutions on `[0, ∞)`
    (`evolution_fourier_mild`, `fourier_mild_unique`);
  * linearized spectrum: each `e_n` is an eigenmode with growth rate
    `σ(n)` (`evolution_fourierMode`); exponential stability when
    `σ ≤ -γ` (`evolution_exponentially_stable`) and modal instability when
    some `σ(n₀) > 0` (`evolution_mode_unbounded`);
  * the M7 linear symbol is bounded above (`m7SymbolAtWavenumber_le`), so the
    linear M7 flow is globally well posed (`m7_linear_well_posed`), and the
    Swift–Hohenberg shell mode is unstable at onset
    (`swiftHohenberg_shell_unstable`).

  The nonlinear curvature term is *not* included here; nonlinear local
  well-posedness (Duhamel fixed point) remains open.
-/

import Mathlib
import WCTLean.FourierSpectral

namespace WCTLean

open MeasureTheory Filter Topology AddCircle
open scoped InnerProductSpace ENNReal

noncomputable section

variable {T : ℝ} [hT : Fact (0 < T)]

/-! ### Fourier coefficients and extensionality -/

theorem fourierBasis_repr_eq (f : L2Circle T) (n : ℤ) :
    fourierBasis.repr f n = fourierCoeff f n :=
  fourierBasis_repr f n

/-- Two `L²` functions with the same Fourier coefficients are equal. -/
theorem L2Circle_ext {f g : L2Circle T} (h : ∀ n, fourierCoeff f n = fourierCoeff g n) :
    f = g := by
  apply fourierBasis.repr.injective
  apply lp.ext
  funext n
  rw [fourierBasis_repr_eq, fourierBasis_repr_eq, h n]

theorem fourierCoeff_sub (f g : L2Circle T) (n : ℤ) :
    fourierCoeff (↑↑(f - g) : AddCircle T → ℂ) n = fourierCoeff f n - fourierCoeff g n := by
  rw [← fourierBasis_repr_eq, map_sub, ← fourierBasis_repr_eq, ← fourierBasis_repr_eq]
  rfl

theorem fourierCoeff_smul (c : ℂ) (f : L2Circle T) (n : ℤ) :
    fourierCoeff (↑↑(c • f) : AddCircle T → ℂ) n = c * fourierCoeff f n := by
  rw [← fourierBasis_repr_eq, map_smul, ← fourierBasis_repr_eq]
  rfl

/-! ### The evolution operator -/

/-- A real Fourier symbol with an explicit upper bound. -/
structure BoundedAboveSymbol where
  σ : ℤ → ℝ
  μ : ℝ
  le : ∀ n, σ n ≤ μ

/-- The time-`t` multiplier `e^{t⁺ σ(n)}` (`t⁺ = max t 0`). -/
def evolutionMultiplier (s : BoundedAboveSymbol) (t : ℝ) (n : ℤ) : ℝ :=
  Real.exp (max t 0 * s.σ n)

theorem evolutionMultiplier_pos (s : BoundedAboveSymbol) (t : ℝ) (n : ℤ) :
    0 < evolutionMultiplier s t n :=
  Real.exp_pos _

theorem evolutionMultiplier_le (s : BoundedAboveSymbol) (t : ℝ) (n : ℤ) :
    evolutionMultiplier s t n ≤ Real.exp (max t 0 * s.μ) := by
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_left (s.le n) (le_max_right t 0)

theorem evolutionMultiplier_of_nonneg (s : BoundedAboveSymbol) {t : ℝ} (ht : 0 ≤ t) (n : ℤ) :
    evolutionMultiplier s t n = Real.exp (t * s.σ n) := by
  simp [evolutionMultiplier, max_eq_left ht]

theorem memℓp_two_of_le {a b : ℤ → ℂ} (ha : Memℓp a 2) (C : ℝ)
    (hab : ∀ n, ‖b n‖ ≤ C * ‖a n‖) : Memℓp b 2 := by
  apply memℓp_gen
  have hs := ha.summable (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hs ⊢
  refine (hs.mul_left (C ^ 2)).of_nonneg_of_le (fun n => sq_nonneg _) (fun n => ?_)
  calc ‖b n‖ ^ 2 ≤ (C * ‖a n‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hab n) 2
    _ = C ^ 2 * ‖a n‖ ^ 2 := by ring

theorem memℓp_evolution (s : BoundedAboveSymbol) (t : ℝ) (f : L2Circle T) :
    Memℓp (fun n => ((evolutionMultiplier s t n : ℝ) : ℂ) * fourierBasis.repr f n) 2 :=
  memℓp_two_of_le (fourierBasis.repr f).2 (Real.exp (max t 0 * s.μ)) fun n => by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (evolutionMultiplier_pos s t n)]
    exact mul_le_mul_of_nonneg_right (evolutionMultiplier_le s t n) (norm_nonneg _)

/-- **The linear evolution operator** `S(t) f = ∑ e^{t⁺σ(n)} f̂(n) e_n`. -/
def evolution (s : BoundedAboveSymbol) (t : ℝ) (f : L2Circle T) : L2Circle T :=
  fourierBasis.repr.symm ⟨_, memℓp_evolution s t f⟩

/-- Fourier coefficients of the evolved function. -/
theorem fourierCoeff_evolution (s : BoundedAboveSymbol) (t : ℝ) (f : L2Circle T) (n : ℤ) :
    fourierCoeff (evolution s t f) n = (evolutionMultiplier s t n : ℂ) * fourierCoeff f n := by
  rw [← fourierBasis_repr_eq, evolution, LinearIsometryEquiv.apply_symm_apply,
    ← fourierBasis_repr_eq]

theorem evolution_zero (s : BoundedAboveSymbol) (f : L2Circle T) : evolution s 0 f = f :=
  L2Circle_ext fun n => by
    rw [fourierCoeff_evolution, evolutionMultiplier_of_nonneg s le_rfl]
    simp

theorem evolution_of_nonpos (s : BoundedAboveSymbol) {t : ℝ} (ht : t ≤ 0) (f : L2Circle T) :
    evolution s t f = f :=
  L2Circle_ext fun n => by
    rw [fourierCoeff_evolution]
    simp [evolutionMultiplier, max_eq_right ht]

/-- **Semigroup law** for nonnegative times. -/
theorem evolution_add_time (s : BoundedAboveSymbol) {t r : ℝ} (ht : 0 ≤ t) (hr : 0 ≤ r)
    (f : L2Circle T) : evolution s (t + r) f = evolution s t (evolution s r f) :=
  L2Circle_ext fun n => by
    rw [fourierCoeff_evolution, fourierCoeff_evolution, fourierCoeff_evolution,
      evolutionMultiplier_of_nonneg s (add_nonneg ht hr), evolutionMultiplier_of_nonneg s ht,
      evolutionMultiplier_of_nonneg s hr, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
    congr 3
    ring

theorem evolution_sub (s : BoundedAboveSymbol) (t : ℝ) (f g : L2Circle T) :
    evolution s t (f - g) = evolution s t f - evolution s t g :=
  L2Circle_ext fun n => by
    rw [fourierCoeff_sub, fourierCoeff_evolution, fourierCoeff_evolution,
      fourierCoeff_evolution, fourierCoeff_sub]
    ring

theorem evolution_smul (s : BoundedAboveSymbol) (t : ℝ) (c : ℂ) (f : L2Circle T) :
    evolution s t (c • f) = c • evolution s t f :=
  L2Circle_ext fun n => by
    rw [fourierCoeff_smul, fourierCoeff_evolution, fourierCoeff_evolution, fourierCoeff_smul]
    ring

/-- **Global bound** `‖S(t)f‖ ≤ e^{μ t⁺}‖f‖`. -/
theorem norm_evolution_le (s : BoundedAboveSymbol) (t : ℝ) (f : L2Circle T) :
    ‖evolution s t f‖ ≤ Real.exp (max t 0 * s.μ) * ‖f‖ := by
  have h1 := hasSum_norm_sq_fourierCoeff (evolution s t f)
  have h2 := (hasSum_norm_sq_fourierCoeff f).mul_left (Real.exp (max t 0 * s.μ) ^ 2)
  have hle := hasSum_le (fun n => by
    rw [fourierCoeff_evolution, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (evolutionMultiplier_pos s t n), mul_pow]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (evolutionMultiplier_pos s t n).le (evolutionMultiplier_le s t n) 2)
      (sq_nonneg _)) h1 h2
  rw [← mul_pow] at hle
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))).mp hle

/-- **Lipschitz dependence on the initial data.** -/
theorem norm_evolution_sub_le (s : BoundedAboveSymbol) (t : ℝ) (f g : L2Circle T) :
    ‖evolution s t f - evolution s t g‖ ≤ Real.exp (max t 0 * s.μ) * ‖f - g‖ := by
  rw [← evolution_sub]
  exact norm_evolution_le s t (f - g)

/-- **Strong continuity** at `t = 0`. -/
theorem tendsto_evolution_zero (s : BoundedAboveSymbol) (f : L2Circle T) :
    Tendsto (fun t => evolution s t f) (𝓝 0) (𝓝 f) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  -- Parseval for the difference
  have hpars : ∀ t, ‖evolution s t f - f‖ ^ 2 =
      ∑' n, ‖((evolutionMultiplier s t n : ℂ) - 1) * fourierCoeff f n‖ ^ 2 := by
    intro t
    rw [← (hasSum_norm_sq_fourierCoeff (evolution s t f - f)).tsum_eq]
    congr 1
    funext n
    rw [fourierCoeff_sub, fourierCoeff_evolution]
    ring_nf
  set B : ℝ := Real.exp (max s.μ 0) + 1 with hB
  have hbound : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ n,
      ‖‖((evolutionMultiplier s t n : ℂ) - 1) * fourierCoeff f n‖ ^ 2‖ ≤
        B ^ 2 * ‖fourierCoeff f n‖ ^ 2 := by
    filter_upwards [Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1)]
      with t ht n
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), norm_mul, mul_pow]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply pow_le_pow_left₀ (norm_nonneg _)
    have hm : evolutionMultiplier s t n ≤ Real.exp (max s.μ 0) := by
      refine (evolutionMultiplier_le s t n).trans (Real.exp_le_exp.mpr ?_)
      have h0 : 0 ≤ max t 0 := le_max_right t 0
      have h1 : max t 0 ≤ 1 := max_le ht.2.le zero_le_one
      rcases le_total 0 s.μ with hμ | hμ
      · calc max t 0 * s.μ ≤ 1 * s.μ := mul_le_mul_of_nonneg_right h1 hμ
          _ = s.μ := one_mul _
          _ ≤ max s.μ 0 := le_max_left _ _
      · calc max t 0 * s.μ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h0 hμ
          _ ≤ max s.μ 0 := le_max_right _ _
    calc ‖((evolutionMultiplier s t n : ℂ) - 1)‖ ≤ ‖(evolutionMultiplier s t n : ℂ)‖ + ‖(1 : ℂ)‖ :=
          norm_sub_le _ _
      _ = evolutionMultiplier s t n + 1 := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (evolutionMultiplier_pos s t n),
            norm_one]
      _ ≤ B := by rw [hB]; linarith
  have hsum : Summable fun n => B ^ 2 * ‖fourierCoeff f n‖ ^ 2 :=
    (hasSum_norm_sq_fourierCoeff f).summable.mul_left _
  have hlim : ∀ n, Tendsto (fun t => ‖((evolutionMultiplier s t n : ℂ) - 1) *
      fourierCoeff f n‖ ^ 2) (𝓝 0) (𝓝 0) := by
    intro n
    have hc : Continuous fun t : ℝ => evolutionMultiplier s t n := by
      unfold evolutionMultiplier; fun_prop
    have h0 : evolutionMultiplier s 0 n = 1 := by simp [evolutionMultiplier]
    have hct : Tendsto (fun t : ℝ => ‖((evolutionMultiplier s t n : ℂ) - 1) *
        fourierCoeff f n‖ ^ 2) (𝓝 0)
        (𝓝 (‖((evolutionMultiplier s 0 n : ℂ) - 1) * fourierCoeff f n‖ ^ 2)) :=
      ((((Complex.continuous_ofReal.comp hc).sub continuous_const).mul
        continuous_const).norm.pow 2).tendsto 0
    rwa [h0, Complex.ofReal_one, sub_self, zero_mul, norm_zero,
      zero_pow two_ne_zero] at hct
  have htsum := tendsto_tsum_of_dominated_convergence hsum hlim hbound
  simp only [tsum_zero] at htsum
  have hsq : Tendsto (fun t => ‖evolution s t f - f‖ ^ 2) (𝓝 0) (𝓝 0) := by
    simp_rw [hpars]; exact htsum
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hsq
  simp only [Real.sqrt_zero] at hsqrt
  refine hsqrt.congr fun t => ?_
  exact Real.sqrt_sq (norm_nonneg _)

/-! ### Fourier-mild solutions: existence and uniqueness -/

/-- Each Fourier mode of `t ↦ S(t)f` solves `ĉ' = σ(n) ĉ` on `[0, ∞)`. -/
theorem evolution_fourier_mild (s : BoundedAboveSymbol) (f : L2Circle T) (n : ℤ) {t : ℝ}
    (ht : 0 ≤ t) :
    HasDerivWithinAt (fun r => fourierCoeff (evolution s r f) n)
      ((s.σ n : ℂ) * fourierCoeff (evolution s t f) n) (Set.Ici 0) t := by
  have hexp : HasDerivAt (fun r : ℝ => ((Real.exp (r * s.σ n) : ℝ) : ℂ) * fourierCoeff f n)
      (((Real.exp (t * s.σ n) * s.σ n : ℝ) : ℂ) * fourierCoeff f n) t := by
    have h := ((hasDerivAt_id t).mul_const (s.σ n)).exp.ofReal_comp.mul_const (fourierCoeff f n)
    simpa using h
  have heq : ∀ r ∈ Set.Ici (0 : ℝ), fourierCoeff (evolution s r f) n =
      ((Real.exp (r * s.σ n) : ℝ) : ℂ) * fourierCoeff f n := by
    intro r hr
    rw [fourierCoeff_evolution, evolutionMultiplier_of_nonneg s hr]
  have hderiv := hexp.hasDerivWithinAt (s := Set.Ici 0)
  refine (hderiv.congr heq (heq t ht)).congr_deriv ?_
  rw [fourierCoeff_evolution, evolutionMultiplier_of_nonneg s ht]
  push_cast
  ring

/-- **Uniqueness of Fourier-mild solutions.**  If every Fourier mode of
`u : ℝ → L²` solves `ĉ' = σ(n) ĉ` on `[0, ∞)` (one-sided derivatives) and
`u 0 = f`, then `u t = S(t) f` for all `t ≥ 0`. -/
theorem fourier_mild_unique (s : BoundedAboveSymbol) (f : L2Circle T) (u : ℝ → L2Circle T)
    (h0 : u 0 = f)
    (hode : ∀ n, ∀ t, 0 ≤ t → HasDerivWithinAt (fun r => fourierCoeff (u r) n)
      ((s.σ n : ℂ) * fourierCoeff (u t) n) (Set.Ici 0) t) :
    ∀ t, 0 ≤ t → u t = evolution s t f := by
  intro t ht
  apply L2Circle_ext
  intro n
  set c : ℝ → ℂ := fun r => fourierCoeff (u r) n with hc_def
  set G : ℝ → ℂ := fun r => ((Real.exp (-(r * s.σ n)) : ℝ) : ℂ) * c r with hG_def
  have hGd : ∀ r, 0 ≤ r → HasDerivWithinAt G 0 (Set.Ici 0) r := by
    intro r hr
    have he : HasDerivAt (fun r : ℝ => ((Real.exp (-(r * s.σ n)) : ℝ) : ℂ))
        (((Real.exp (-(r * s.σ n)) * -(s.σ n) : ℝ) : ℂ)) r := by
      have h := ((hasDerivAt_id r).mul_const (s.σ n)).neg.exp.ofReal_comp
      simpa using h
    have h := he.hasDerivWithinAt.mul (hode n r hr)
    convert h using 1
    push_cast
    ring
  have hcont : ContinuousOn G (Set.Icc 0 t) := fun r hr =>
    ((hGd r hr.1).continuousWithinAt).mono (fun x hx => hx.1)
  have hconst := constant_of_has_deriv_right_zero hcont
    (fun r hr => (hGd r hr.1).mono (Set.Ici_subset_Ici.mpr hr.1)) t ⟨ht, le_rfl⟩
  simp only [hG_def, hc_def, zero_mul, neg_zero, Real.exp_zero, Complex.ofReal_one,
    one_mul, h0] at hconst
  rw [fourierCoeff_evolution, evolutionMultiplier_of_nonneg s ht, ← hconst]
  rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add, add_neg_cancel, Real.exp_zero,
    Complex.ofReal_one, one_mul]

/-! ### Linearized spectrum: stability and instability -/

/-- Each Fourier mode is an eigenmode: `S(t) e_k = e^{t σ(k)} e_k`. -/
theorem evolution_fourierMode (s : BoundedAboveSymbol) {t : ℝ} (ht : 0 ≤ t) (k : ℤ) :
    evolution s t (fourierMode (T := T) k) = ((Real.exp (t * s.σ k) : ℝ) : ℂ) • fourierMode k :=
  L2Circle_ext fun n => by
    rw [fourierCoeff_evolution, fourierCoeff_smul, fourierCoeff_fourierMode,
      evolutionMultiplier_of_nonneg s ht]
    split_ifs with h
    · subst h; rfl
    · simp

/-- **Exponential stability** when the whole spectrum lies below `-γ`. -/
theorem evolution_exponentially_stable (σ : ℤ → ℝ) (γ : ℝ) (hσ : ∀ n, σ n ≤ -γ)
    {t : ℝ} (ht : 0 ≤ t) (f : L2Circle T) :
    ‖evolution ⟨σ, -γ, hσ⟩ t f‖ ≤ Real.exp (-(γ * t)) * ‖f‖ := by
  have h := norm_evolution_le ⟨σ, -γ, hσ⟩ t f
  rwa [max_eq_left ht, show t * -γ = -(γ * t) by ring] at h

/-- **Modal instability.**  If `σ(k) > 0`, the mode `e_k` grows without
bound: `‖S(t) e_k‖ = e^{t σ(k)} → ∞`. -/
theorem evolution_mode_unbounded (s : BoundedAboveSymbol) (k : ℤ) (hk : 0 < s.σ k) :
    Tendsto (fun t => ‖evolution s t (fourierMode (T := T) k)‖) atTop atTop := by
  have hnorm : ∀ᶠ t in atTop, ‖evolution s t (fourierMode (T := T) k)‖ =
      Real.exp (t * s.σ k) := by
    filter_upwards [eventually_ge_atTop 0] with t ht
    rw [evolution_fourierMode s ht, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), (fourierMode_orthonormal (T := T)).1 k, mul_one]
  refine (Real.tendsto_exp_atTop.comp
    (tendsto_id.atTop_mul_const hk)).congr' ?_
  filter_upwards [hnorm] with t ht
  rw [ht]
  rfl

/-! ### The M7 linear symbol -/

/-- M7 linear symbol `c₁(σ₀² - k²) - c₂(k⋆² - k²)²`. -/
def m7SymbolAtWavenumber (c₁ σ₀ c₂ kStar k : ℝ) : ℝ :=
  c₁ * (σ₀ ^ 2 - k ^ 2) - c₂ * (kStar ^ 2 - k ^ 2) ^ 2

/-- Uniform upper bound of the M7 linear symbol for `c₂ > 0`. -/
def m7SymbolUpperBound (c₁ σ₀ c₂ kStar : ℝ) : ℝ :=
  c₁ * σ₀ ^ 2 - c₂ * kStar ^ 4 + (2 * c₂ * kStar ^ 2 - c₁) ^ 2 / (4 * c₂)

theorem m7SymbolAtWavenumber_le (c₁ σ₀ c₂ kStar k : ℝ) (hc₂ : 0 < c₂) :
    m7SymbolAtWavenumber c₁ σ₀ c₂ kStar k ≤ m7SymbolUpperBound c₁ σ₀ c₂ kStar := by
  unfold m7SymbolAtWavenumber m7SymbolUpperBound
  have key : c₁ * σ₀ ^ 2 - c₂ * kStar ^ 4 + (2 * c₂ * kStar ^ 2 - c₁) ^ 2 / (4 * c₂) -
      (c₁ * (σ₀ ^ 2 - k ^ 2) - c₂ * (kStar ^ 2 - k ^ 2) ^ 2) =
        c₂ * (k ^ 2 - (2 * c₂ * kStar ^ 2 - c₁) / (2 * c₂)) ^ 2 := by
    field_simp
    ring
  have : 0 ≤ c₂ * (k ^ 2 - (2 * c₂ * kStar ^ 2 - c₁) / (2 * c₂)) ^ 2 :=
    mul_nonneg hc₂.le (sq_nonneg _)
  linarith

/-- The M7 linear symbol on the circle of circumference `T`, with its bound. -/
def m7Symbol (T c₁ σ₀ c₂ kStar : ℝ) (hc₂ : 0 < c₂) : BoundedAboveSymbol where
  σ := fun n => m7SymbolAtWavenumber c₁ σ₀ c₂ kStar (circleWavenumber T n)
  μ := m7SymbolUpperBound c₁ σ₀ c₂ kStar
  le := fun _ => m7SymbolAtWavenumber_le c₁ σ₀ c₂ kStar _ hc₂

/-- **Global well-posedness of the linear M7 flow** on `L²(AddCircle T)`:
for every initial datum there is a unique Fourier-mild solution on `[0, ∞)`,
it satisfies the bound `‖u(t)‖ ≤ e^{Ct}‖f‖`, and depends Lipschitz
continuously on the data. -/
theorem m7_linear_well_posed (c₁ σ₀ c₂ kStar : ℝ) (hc₂ : 0 < c₂) (f : L2Circle T) :
    (∀ n t, 0 ≤ t → HasDerivWithinAt
        (fun r => fourierCoeff (evolution (m7Symbol T c₁ σ₀ c₂ kStar hc₂) r f) n)
        (((m7Symbol T c₁ σ₀ c₂ kStar hc₂).σ n : ℂ) *
          fourierCoeff (evolution (m7Symbol T c₁ σ₀ c₂ kStar hc₂) t f) n) (Set.Ici 0) t) ∧
      (∀ u : ℝ → L2Circle T, u 0 = f →
        (∀ n t, 0 ≤ t → HasDerivWithinAt (fun r => fourierCoeff (u r) n)
          (((m7Symbol T c₁ σ₀ c₂ kStar hc₂).σ n : ℂ) * fourierCoeff (u t) n) (Set.Ici 0) t) →
        ∀ t, 0 ≤ t → u t = evolution (m7Symbol T c₁ σ₀ c₂ kStar hc₂) t f) ∧
      (∀ t, 0 ≤ t → ‖evolution (m7Symbol T c₁ σ₀ c₂ kStar hc₂) t f‖ ≤
        Real.exp (t * m7SymbolUpperBound c₁ σ₀ c₂ kStar) * ‖f‖) ∧
      (∀ t g, ‖evolution (m7Symbol T c₁ σ₀ c₂ kStar hc₂) t f -
          evolution (m7Symbol T c₁ σ₀ c₂ kStar hc₂) t g‖ ≤
        Real.exp (max t 0 * m7SymbolUpperBound c₁ σ₀ c₂ kStar) * ‖f - g‖) := by
  refine ⟨fun n t ht => evolution_fourier_mild _ f n ht,
    fun u hu0 hode => fourier_mild_unique _ f u hu0 hode, fun t ht => ?_,
    fun t g => norm_evolution_sub_le _ t f g⟩
  have h := norm_evolution_le (m7Symbol T c₁ σ₀ c₂ kStar hc₂) t f
  rwa [max_eq_left ht] at h

/-- Swift–Hohenberg symbol of `Models/BandPass.lean` on the circle. -/
def swiftHohenbergSymbol (T mu b kStar : ℝ) (hb : 0 ≤ b) : BoundedAboveSymbol where
  σ := fun n => swiftHohenbergLinearSymbol mu b (circleWavenumber T n) kStar
  μ := mu
  le := fun _ => swiftHohenbergLinearSymbol_le_mu mu b _ kStar hb

/-- **Onset instability on the circle.**  If the selected shell is resonant
with a circle mode (`k⋆ = 2πk/T`) and `μ > 0`, that mode grows without
bound under the linear Swift–Hohenberg flow. -/
theorem swiftHohenberg_shell_unstable (mu b : ℝ) (hb : 0 ≤ b) (hmu : 0 < mu) (k : ℤ) :
    Tendsto (fun t => ‖evolution (swiftHohenbergSymbol T mu b (circleWavenumber T k) hb) t
      (fourierMode (T := T) k)‖) atTop atTop :=
  evolution_mode_unbounded _ k (by
    show 0 < swiftHohenbergLinearSymbol mu b (circleWavenumber T k) (circleWavenumber T k)
    rw [swiftHohenbergLinearSymbol_at_shell]
    exact hmu)

/-- **Subcritical stability.**  For `μ < 0` the linear Swift–Hohenberg flow
is exponentially stable on `L²(AddCircle T)`. -/
theorem swiftHohenberg_subcritical_stable (mu b kStar : ℝ) (hb : 0 ≤ b) {t : ℝ} (ht : 0 ≤ t)
    (f : L2Circle T) :
    ‖evolution (swiftHohenbergSymbol T mu b kStar hb) t f‖ ≤ Real.exp (t * mu) * ‖f‖ := by
  have h := norm_evolution_le (swiftHohenbergSymbol T mu b kStar hb) t f
  rwa [max_eq_left ht] at h

end

end WCTLean
