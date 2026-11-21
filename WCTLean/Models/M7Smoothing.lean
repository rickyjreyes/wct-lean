/-
  WCTLean/Models/M7Smoothing.lean

  Issue #19: parabolic `L² → Ḣ²` smoothing of the linear M7 evolution on
  `L²(AddCircle T)`, the linear estimate required by a Duhamel fixed point
  for the second-order curvature nonlinearity.

  With `k_n = 2πn/T` and the spectral Laplacian `Δe_n = -k_n² e_n`:

  * `m7Symbol_coercive`: the M7 symbol satisfies the coercive bound
    `σ(k) ≤ C - (c₂/2) k⁴` (`c₂ > 0`);
  * `evolution_H2_smoothing`: for any symbol with `σ(n) ≤ C - a k_n⁴`
    (`a > 0`) and every `t > 0`, `S(t)f` has square-summable spectral
    Laplacian coefficients and
    `∑ₙ |k_n² (S(t)f)^(n)|² ≤ e^{2tC}/(2at) ‖f‖²`;
  * `m7_H2_smoothing`: the M7 instance, `‖ΔS(t)f‖ ≤ e^{tC}(c₂t)^{-1/2}‖f‖` in
    the spectral sense;
  * `smoothing_rate_integrable`: the rate `t^{-1/2}` is integrable on
    `(0, τ)`, as the Duhamel argument requires.

  The nonlinear fixed point itself is not formalized here.
-/

import Mathlib
import WCTLean.Models.M7LinearSemigroup

namespace WCTLean

open MeasureTheory Filter Topology AddCircle

noncomputable section

variable {T : ℝ} [hT : Fact (0 < T)]

/-- `q² e^{-a q²} ≤ 1/a` for `a > 0`. -/
theorem sq_mul_exp_neg_le (q a : ℝ) (ha : 0 < a) :
    q ^ 2 * Real.exp (-(a * q ^ 2)) ≤ 1 / a := by
  have hx : a * q ^ 2 ≤ Real.exp (a * q ^ 2) := by
    linarith [Real.add_one_le_exp (a * q ^ 2)]
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ (Real.exp_pos _) ha]
  nlinarith

/-- Coercivity constant of the M7 symbol. -/
def m7CoerciveConstant (c₁ σ₀ c₂ kStar : ℝ) : ℝ :=
  c₁ * σ₀ ^ 2 - c₂ * kStar ^ 4 + (2 * c₂ * kStar ^ 2 - c₁) ^ 2 / (2 * c₂)

/-- **Coercive bound of the M7 symbol**: `σ(k) ≤ C - (c₂/2) k⁴`. -/
theorem m7Symbol_coercive (c₁ σ₀ c₂ kStar k : ℝ) (hc₂ : 0 < c₂) :
    m7SymbolAtWavenumber c₁ σ₀ c₂ kStar k ≤
      m7CoerciveConstant c₁ σ₀ c₂ kStar - c₂ / 2 * (k ^ 2) ^ 2 := by
  unfold m7SymbolAtWavenumber m7CoerciveConstant
  have key : (c₁ * σ₀ ^ 2 - c₂ * kStar ^ 4 + (2 * c₂ * kStar ^ 2 - c₁) ^ 2 / (2 * c₂) -
      c₂ / 2 * (k ^ 2) ^ 2) - (c₁ * (σ₀ ^ 2 - k ^ 2) - c₂ * (kStar ^ 2 - k ^ 2) ^ 2) =
        c₂ / 2 * (k ^ 2 - (2 * c₂ * kStar ^ 2 - c₁) / c₂) ^ 2 := by
    field_simp
    ring
  have : 0 ≤ c₂ / 2 * (k ^ 2 - (2 * c₂ * kStar ^ 2 - c₁) / c₂) ^ 2 := by positivity
  linarith

/-- **Spectral `L² → Ḣ²` smoothing.**  If `σ(n) ≤ C - a k_n⁴` with `a > 0`,
then for every `t > 0` the spectral Laplacian coefficients `k_n² (S(t)f)^(n)`
are square summable with
`∑ |k_n² (S(t)f)^(n)|² ≤ e^{2tC}/(2at) ‖f‖²`. -/
theorem evolution_H2_smoothing (s : BoundedAboveSymbol) (C a : ℝ) (ha : 0 < a)
    (hcoer : ∀ n, s.σ n ≤ C - a * (circleWavenumber T n ^ 2) ^ 2) {t : ℝ} (ht : 0 < t)
    (f : L2Circle T) :
    Summable (fun n => ‖((circleWavenumber T n ^ 2 : ℝ) : ℂ) *
        fourierCoeff (evolution s t f) n‖ ^ 2) ∧
      ∑' n, ‖((circleWavenumber T n ^ 2 : ℝ) : ℂ) * fourierCoeff (evolution s t f) n‖ ^ 2 ≤
        Real.exp (2 * t * C) / (2 * a * t) * ‖f‖ ^ 2 := by
  set K : ℝ := Real.exp (2 * t * C) / (2 * a * t) with hK_def
  have hpars := hasSum_norm_sq_fourierCoeff f
  have hterm : ∀ n, ‖((circleWavenumber T n ^ 2 : ℝ) : ℂ) * fourierCoeff (evolution s t f) n‖ ^ 2 ≤
      K * ‖fourierCoeff f n‖ ^ 2 := by
    intro n
    set q := circleWavenumber T n ^ 2 with hq
    rw [fourierCoeff_evolution, evolutionMultiplier_of_nonneg s ht.le, norm_mul, norm_mul,
      Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by rw [hq]; positivity), abs_of_pos (Real.exp_pos _)]
    have hexp : Real.exp (t * s.σ n) ^ 2 ≤ Real.exp (2 * t * C) * Real.exp (-(2 * a * t * q ^ 2)) := by
      rw [← Real.exp_add, ← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      have := hcoer n
      rw [← hq] at this
      have hmul := mul_le_mul_of_nonneg_left this ht.le
      push_cast
      nlinarith
    have hq2 : q ^ 2 * Real.exp (-(2 * a * t * q ^ 2)) ≤ 1 / (2 * a * t) := by
      have := sq_mul_exp_neg_le q (2 * a * t) (by positivity)
      simpa using this
    calc (q * (Real.exp (t * s.σ n) * ‖fourierCoeff f n‖)) ^ 2
        = q ^ 2 * Real.exp (t * s.σ n) ^ 2 * ‖fourierCoeff f n‖ ^ 2 := by ring
      _ ≤ q ^ 2 * (Real.exp (2 * t * C) * Real.exp (-(2 * a * t * q ^ 2))) *
            ‖fourierCoeff f n‖ ^ 2 := by
          gcongr
      _ = Real.exp (2 * t * C) * (q ^ 2 * Real.exp (-(2 * a * t * q ^ 2))) *
            ‖fourierCoeff f n‖ ^ 2 := by ring
      _ ≤ Real.exp (2 * t * C) * (1 / (2 * a * t)) * ‖fourierCoeff f n‖ ^ 2 := by
          gcongr
      _ = K * ‖fourierCoeff f n‖ ^ 2 := by rw [hK_def]; ring
  have hsum : Summable fun n => ‖((circleWavenumber T n ^ 2 : ℝ) : ℂ) *
      fourierCoeff (evolution s t f) n‖ ^ 2 :=
    (hpars.summable.mul_left K).of_nonneg_of_le (fun n => sq_nonneg _) hterm
  refine ⟨hsum, ?_⟩
  calc ∑' n, ‖((circleWavenumber T n ^ 2 : ℝ) : ℂ) * fourierCoeff (evolution s t f) n‖ ^ 2
      ≤ ∑' n, K * ‖fourierCoeff f n‖ ^ 2 := hsum.tsum_le_tsum hterm (hpars.summable.mul_left K)
    _ = K * ‖f‖ ^ 2 := by rw [tsum_mul_left, hpars.tsum_eq]

/-- The M7 symbol with its coercive bound. -/
theorem m7Symbol_coercive_circle (T c₁ σ₀ c₂ kStar : ℝ) (hc₂ : 0 < c₂) (n : ℤ) :
    (m7Symbol T c₁ σ₀ c₂ kStar hc₂).σ n ≤
      m7CoerciveConstant c₁ σ₀ c₂ kStar - c₂ / 2 * (circleWavenumber T n ^ 2) ^ 2 :=
  m7Symbol_coercive c₁ σ₀ c₂ kStar _ hc₂

/-- **M7 parabolic smoothing.**  For `c₂ > 0` and `t > 0`,
`∑ |k_n² (S(t)f)^(n)|² ≤ e^{2tC}/(c₂ t) ‖f‖²`, i.e. the spectral Laplacian of
the linear M7 evolution satisfies `‖ΔS(t)f‖ ≤ e^{tC}(c₂t)^{-1/2}‖f‖`. -/
theorem m7_H2_smoothing (c₁ σ₀ c₂ kStar : ℝ) (hc₂ : 0 < c₂) {t : ℝ} (ht : 0 < t)
    (f : L2Circle T) :
    Summable (fun n => ‖((circleWavenumber T n ^ 2 : ℝ) : ℂ) *
        fourierCoeff (evolution (m7Symbol T c₁ σ₀ c₂ kStar hc₂) t f) n‖ ^ 2) ∧
      ∑' n, ‖((circleWavenumber T n ^ 2 : ℝ) : ℂ) *
          fourierCoeff (evolution (m7Symbol T c₁ σ₀ c₂ kStar hc₂) t f) n‖ ^ 2 ≤
        Real.exp (2 * t * m7CoerciveConstant c₁ σ₀ c₂ kStar) / (c₂ * t) * ‖f‖ ^ 2 := by
  have h := evolution_H2_smoothing (T := T) (m7Symbol T c₁ σ₀ c₂ kStar hc₂)
    (m7CoerciveConstant c₁ σ₀ c₂ kStar) (c₂ / 2) (by positivity)
    (m7Symbol_coercive_circle T c₁ σ₀ c₂ kStar hc₂) ht f
  refine ⟨h.1, h.2.trans_eq ?_⟩
  congr 1
  field_simp

/-- The smoothing rate `t^{-1/2}` is integrable near `t = 0`. -/
theorem smoothing_rate_integrable (τ : ℝ) (hτ : 0 < τ) :
    IntegrableOn (fun t : ℝ => t ^ (-(1 / 2 : ℝ))) (Set.Ioo 0 τ) :=
  (intervalIntegral.integrableOn_Ioo_rpow_iff hτ).mpr (by norm_num)

end

end WCTLean
