/-
  WCTLean/FourierSpectral.lean

  Issue #23: genuine function-space Fourier spectral projection.

  Setting: the Hilbert space `L²(AddCircle T; ℂ)` for the *normalized* Haar
  probability measure on the circle of circumference `T > 0`, with the
  Fourier modes `e_n = fourierLp 2 n` (`e_n(x) = exp (2π i n x / T)`).
  This is a periodic one-dimensional model; it is *not* the whole-space
  WCT setting.

  Proved here (all kernel-checked, no new axioms):

  * `spectralProjection S` (finite band `S : Finset ℤ`) coincides with the
    orthogonal projection onto `span {e_n : n ∈ S}`
    (`spectralProjection_eq_starProjection`);
  * it is idempotent, self-adjoint, and acts diagonally on Fourier
    coefficients;
  * finite Parseval/Pythagoras: `‖P_S f‖² = ∑_{n∈S} |f̂ n|²` and
    `‖f‖² = ‖P_S f‖² + ‖f - P_S f‖²`, hence Bessel and the exact remainder
    formula;
  * best approximation in the band;
  * the *infinite* spectral resolution: `P_S f → f` along the directed
    system of finite bands, the symmetric partial sums
    `P_{[-N,N]} f → f` in `L²`, and Parseval in norm form
    `HasSum (fun n => ‖f̂ n‖²) ‖f‖²`;
  * band-limited Fourier multipliers (the scalar WCT spectral symbols act
    this way): eigenvectors, quadratic-form identity and the coercivity
    bound from a symbol bound.
-/

import Mathlib
import WCTLean.Models.BandPass

namespace WCTLean

open MeasureTheory Filter Topology ComplexConjugate AddCircle
open scoped InnerProductSpace

noncomputable section

section FourierSpectral

variable {T : ℝ} [hT : Fact (0 < T)]

/-- The Hilbert space `L²(AddCircle T; ℂ)` with normalized Haar measure. -/
abbrev L2Circle (T : ℝ) [Fact (0 < T)] : Type :=
  Lp ℂ 2 (@haarAddCircle T _)

/-- The Fourier mode `e_n` as an element of `L²(AddCircle T)`. -/
abbrev fourierMode (n : ℤ) : L2Circle T :=
  fourierLp 2 n

/-- The Fourier modes are orthonormal in `L²(AddCircle T)`. -/
theorem fourierMode_orthonormal : Orthonormal ℂ (fourierMode (T := T)) :=
  orthonormal_fourier

/-- The `n`-th Fourier coefficient is the `L²` inner product with `e_n`. -/
theorem inner_fourierMode_eq_fourierCoeff (f : L2Circle T) (n : ℤ) :
    ⟪fourierMode n, f⟫_ℂ = fourierCoeff f n := by
  rw [← fourierBasis_repr, fourierBasis.repr_apply_apply, coe_fourierBasis]

/-- Finite Fourier spectral projection onto the modes in `S`. -/
def spectralProjection (S : Finset ℤ) (f : L2Circle T) : L2Circle T :=
  ∑ n ∈ S, fourierCoeff f n • fourierMode n

/-- The spectral subspace spanned by the modes in `S`. -/
def spectralSubspace (T : ℝ) [Fact (0 < T)] (S : Finset ℤ) : Submodule ℂ (L2Circle T) :=
  Submodule.span ℂ ((fourierMode (T := T)) '' (S : Set ℤ))

instance spectralSubspace_finiteDimensional (S : Finset ℤ) :
    FiniteDimensional ℂ (spectralSubspace T S) := by
  unfold spectralSubspace
  exact FiniteDimensional.span_of_finite ℂ (S.finite_toSet.image _)

theorem fourierMode_mem_spectralSubspace {S : Finset ℤ} {n : ℤ} (hn : n ∈ S) :
    fourierMode n ∈ spectralSubspace T S :=
  Submodule.subset_span ⟨n, hn, rfl⟩

/-- Inner product of a mode with a finite combination of modes. -/
theorem inner_fourierMode_sum (S : Finset ℤ) (c : ℤ → ℂ) (k : ℤ) :
    ⟪fourierMode (T := T) k, ∑ n ∈ S, c n • fourierMode n⟫_ℂ =
      if k ∈ S then c k else 0 := by
  classical
  have ho := orthonormal_iff_ite.mp (fourierMode_orthonormal (T := T))
  simp only [inner_sum, inner_smul_right, ho, mul_ite, mul_one, mul_zero]
  split_ifs with hk
  · rw [Finset.sum_ite_eq S k c]; simp [hk]
  · rw [Finset.sum_ite_eq S k c]; simp [hk]

/-- The spectral projection acts diagonally on Fourier coefficients. -/
theorem inner_fourierMode_spectralProjection (S : Finset ℤ) (f : L2Circle T) (k : ℤ) :
    ⟪fourierMode k, spectralProjection S f⟫_ℂ = if k ∈ S then fourierCoeff f k else 0 :=
  inner_fourierMode_sum S _ k

/-- Fourier coefficients of the projected function. -/
theorem fourierCoeff_spectralProjection (S : Finset ℤ) (f : L2Circle T) (k : ℤ) :
    fourierCoeff (spectralProjection S f) k = if k ∈ S then fourierCoeff f k else 0 := by
  rw [← inner_fourierMode_eq_fourierCoeff, inner_fourierMode_spectralProjection]

theorem spectralProjection_mem (S : Finset ℤ) (f : L2Circle T) :
    spectralProjection S f ∈ spectralSubspace T S :=
  Submodule.sum_mem _ fun _ hn =>
    Submodule.smul_mem _ _ (fourierMode_mem_spectralSubspace hn)

/-- The remainder `f - P_S f` is orthogonal to every mode in the band. -/
theorem inner_sub_spectralProjection_fourierMode (S : Finset ℤ) (f : L2Circle T)
    {k : ℤ} (hk : k ∈ S) :
    ⟪f - spectralProjection S f, fourierMode k⟫_ℂ = 0 := by
  rw [← inner_conj_symm, inner_sub_right, inner_fourierMode_spectralProjection, if_pos hk,
    inner_fourierMode_eq_fourierCoeff, sub_self, map_zero]

/-- The remainder `f - P_S f` is orthogonal to the whole spectral subspace. -/
theorem inner_sub_spectralProjection_eq_zero (S : Finset ℤ) (f : L2Circle T) :
    ∀ w ∈ spectralSubspace T S, ⟪f - spectralProjection S f, w⟫_ℂ = 0 := by
  intro w hw
  induction hw using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨k, hk, rfl⟩ := hx
      exact inner_sub_spectralProjection_fourierMode S f hk
  | zero => simp
  | add x y _ _ hx hy => rw [inner_add_right, hx, hy, add_zero]
  | smul a x _ hx => rw [inner_smul_right, hx, mul_zero]

/-- **Spectral projection theorem.**  The finite Fourier projection is the
orthogonal projection onto the span of the modes in the band. -/
theorem spectralProjection_eq_starProjection (S : Finset ℤ) (f : L2Circle T) :
    spectralProjection S f = (spectralSubspace T S).starProjection f :=
  (Submodule.eq_starProjection_of_mem_of_inner_eq_zero (spectralProjection_mem S f)
    (inner_sub_spectralProjection_eq_zero S f)).symm

/-- The spectral projection is idempotent. -/
theorem spectralProjection_idem (S : Finset ℤ) (f : L2Circle T) :
    spectralProjection S (spectralProjection S f) = spectralProjection S f := by
  have hcoeff : ∀ n ∈ S, fourierCoeff (spectralProjection S f) n • fourierMode (T := T) n =
      fourierCoeff f n • fourierMode n := by
    intro n hn
    rw [fourierCoeff_spectralProjection, if_pos hn]
  exact Finset.sum_congr rfl hcoeff

/-- The spectral projection is self-adjoint. -/
theorem spectralProjection_inner_symm (S : Finset ℤ) (f g : L2Circle T) :
    ⟪spectralProjection S f, g⟫_ℂ = ⟪f, spectralProjection S g⟫_ℂ := by
  unfold spectralProjection
  rw [sum_inner, inner_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [inner_smul_left, inner_smul_right, inner_fourierMode_eq_fourierCoeff,
    ← inner_fourierMode_eq_fourierCoeff f n, inner_conj_symm, mul_comm]

/-- Finite Parseval identity for the band: `‖P_S f‖² = ∑_{n∈S} |f̂ n|²`. -/
theorem norm_sq_spectralProjection (S : Finset ℤ) (f : L2Circle T) :
    ‖spectralProjection S f‖ ^ 2 = ∑ n ∈ S, ‖fourierCoeff f n‖ ^ 2 := by
  have h := (fourierMode_orthonormal (T := T)).inner_sum
    (fun n => fourierCoeff f n) (fun n => fourierCoeff f n) S
  have hre := congrArg RCLike.re h
  rw [← @norm_sq_eq_re_inner ℂ] at hre
  unfold spectralProjection
  rw [hre, map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [RCLike.conj_mul]
  norm_cast

/-- Orthogonal splitting `‖f‖² = ‖P_S f‖² + ‖f - P_S f‖²`. -/
theorem norm_sq_eq_spectralProjection_add_remainder (S : Finset ℤ) (f : L2Circle T) :
    ‖f‖ ^ 2 = ‖spectralProjection S f‖ ^ 2 + ‖f - spectralProjection S f‖ ^ 2 := by
  have horth : ⟪spectralProjection S f, f - spectralProjection S f⟫_ℂ = 0 := by
    rw [← inner_conj_symm,
      inner_sub_spectralProjection_eq_zero S f _ (spectralProjection_mem S f), map_zero]
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (spectralProjection S f) (f - spectralProjection S f) horth
  rw [add_sub_cancel] at h
  simp only [sq]
  exact h

/-- Exact remainder: `‖f - P_S f‖² = ‖f‖² - ∑_{n∈S} |f̂ n|²`. -/
theorem norm_sq_sub_spectralProjection (S : Finset ℤ) (f : L2Circle T) :
    ‖f - spectralProjection S f‖ ^ 2 = ‖f‖ ^ 2 - ∑ n ∈ S, ‖fourierCoeff f n‖ ^ 2 := by
  rw [norm_sq_eq_spectralProjection_add_remainder S f, norm_sq_spectralProjection]
  ring

/-- Bessel's inequality for the Fourier band. -/
theorem sum_norm_sq_fourierCoeff_le (S : Finset ℤ) (f : L2Circle T) :
    ∑ n ∈ S, ‖fourierCoeff f n‖ ^ 2 ≤ ‖f‖ ^ 2 := by
  rw [← norm_sq_spectralProjection, norm_sq_eq_spectralProjection_add_remainder S f]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- The spectral projection is a contraction. -/
theorem norm_spectralProjection_le (S : Finset ℤ) (f : L2Circle T) :
    ‖spectralProjection S f‖ ≤ ‖f‖ := by
  have h := norm_sq_eq_spectralProjection_add_remainder S f
  have h2 : ‖spectralProjection S f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
    rw [h]; exact le_add_of_nonneg_right (sq_nonneg _)
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h2

/-- **Best approximation.**  Among all elements of the band, `P_S f` is closest
to `f`. -/
theorem norm_sub_spectralProjection_le (S : Finset ℤ) (f : L2Circle T)
    {g : L2Circle T} (hg : g ∈ spectralSubspace T S) :
    ‖f - spectralProjection S f‖ ≤ ‖f - g‖ := by
  have hmem : spectralProjection S f - g ∈ spectralSubspace T S :=
    Submodule.sub_mem _ (spectralProjection_mem S f) hg
  have horth := inner_sub_spectralProjection_eq_zero S f _ hmem
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (f - spectralProjection S f) (spectralProjection S f - g) horth
  rw [sub_add_sub_cancel] at h
  have h2 : ‖f - spectralProjection S f‖ ^ 2 ≤ ‖f - g‖ ^ 2 := by
    simp only [sq]
    rw [h]
    exact le_add_of_nonneg_right (mul_self_nonneg _)
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h2

/-- **Infinite spectral resolution.**  Along the directed system of finite
bands, `P_S f → f` in `L²`. -/
theorem tendsto_spectralProjection (f : L2Circle T) :
    Tendsto (fun S : Finset ℤ => spectralProjection S f) atTop (𝓝 f) :=
  hasSum_fourier_series_L2 f

/-- The symmetric band `[-N, N]`. -/
def symmetricBand (N : ℕ) : Finset ℤ :=
  Finset.Icc (-(N : ℤ)) N

theorem tendsto_symmetricBand_atTop :
    Tendsto symmetricBand atTop atTop := by
  apply tendsto_atTop_finset_of_monotone
  · intro N M hNM x hx
    simp only [symmetricBand, Finset.mem_Icc] at hx ⊢
    have : (N : ℤ) ≤ M := by exact_mod_cast hNM
    constructor <;> omega
  · intro n
    refine ⟨n.natAbs, ?_⟩
    simp only [symmetricBand, Finset.mem_Icc]
    constructor <;> omega

/-- **Symmetric Fourier partial sums converge in `L²`.** -/
theorem tendsto_symmetric_spectralProjection (f : L2Circle T) :
    Tendsto (fun N : ℕ => spectralProjection (symmetricBand N) f) atTop (𝓝 f) :=
  (tendsto_spectralProjection f).comp tendsto_symmetricBand_atTop

/-- The `L²` remainder of the symmetric partial sums tends to zero. -/
theorem tendsto_norm_sub_symmetric_spectralProjection (f : L2Circle T) :
    Tendsto (fun N : ℕ => ‖f - spectralProjection (symmetricBand N) f‖) atTop (𝓝 0) := by
  have h := (tendsto_symmetric_spectralProjection f).const_sub f
  rw [sub_self] at h
  simpa using h.norm

/-- **Parseval in norm form** (infinite spectral identity):
`∑_n |f̂ n|² = ‖f‖²` as an unconditional sum. -/
theorem hasSum_norm_sq_fourierCoeff (f : L2Circle T) :
    HasSum (fun n : ℤ => ‖fourierCoeff f n‖ ^ 2) (‖f‖ ^ 2) := by
  have h : Tendsto (fun S : Finset ℤ => ‖spectralProjection S f‖ ^ 2) atTop (𝓝 (‖f‖ ^ 2)) :=
    ((tendsto_spectralProjection f).norm).pow 2
  unfold HasSum
  simpa only [norm_sq_spectralProjection] using h

/-- The spectral tail energy `∑_{n∉S} |f̂ n|²` equals the projection error. -/
theorem tsum_tail_eq_norm_sq_sub_spectralProjection (S : Finset ℤ) (f : L2Circle T) :
    ∑' n : {n : ℤ // n ∉ S}, ‖fourierCoeff f n‖ ^ 2 = ‖f - spectralProjection S f‖ ^ 2 := by
  have hs := hasSum_norm_sq_fourierCoeff f
  rw [norm_sq_sub_spectralProjection, ← hs.tsum_eq,
    ← Summable.sum_add_tsum_compl (s := S) hs.summable]
  simp only [add_sub_cancel_left]
  rfl

/-! ### Band-limited Fourier multipliers

The scalar WCT spectral symbols (e.g. the band-pass symbol
`r + a k² - b k⁴` of `Models/BandPass.lean`) act on a finite band as
diagonal Fourier multipliers.  Here the symbol is an arbitrary
`σ : ℤ → ℂ`. -/

/-- Band-limited Fourier multiplier with symbol `σ` on the band `S`. -/
def bandMultiplier (σ : ℤ → ℂ) (S : Finset ℤ) (f : L2Circle T) : L2Circle T :=
  ∑ n ∈ S, (σ n * fourierCoeff f n) • fourierMode n

/-- Multiplier with symbol `1` is the spectral projection. -/
theorem bandMultiplier_one (S : Finset ℤ) (f : L2Circle T) :
    bandMultiplier (fun _ => 1) S f = spectralProjection S f := by
  simp [bandMultiplier, spectralProjection]

/-- Coefficients of the multiplied function. -/
theorem fourierCoeff_bandMultiplier (σ : ℤ → ℂ) (S : Finset ℤ) (f : L2Circle T) (k : ℤ) :
    fourierCoeff (bandMultiplier σ S f) k = if k ∈ S then σ k * fourierCoeff f k else 0 := by
  rw [← inner_fourierMode_eq_fourierCoeff]
  exact inner_fourierMode_sum S _ k

/-- Fourier coefficients of a single mode. -/
theorem fourierCoeff_fourierMode (k n : ℤ) :
    fourierCoeff (fourierMode (T := T) k) n = if n = k then 1 else 0 := by
  rw [← inner_fourierMode_eq_fourierCoeff]
  exact orthonormal_iff_ite.mp (fourierMode_orthonormal (T := T)) n k

/-- **Eigenvectors.**  Each mode in the band is an eigenvector with eigenvalue
`σ k`. -/
theorem bandMultiplier_fourierMode (σ : ℤ → ℂ) {S : Finset ℤ} {k : ℤ} (hk : k ∈ S) :
    bandMultiplier σ S (fourierMode (T := T) k) = σ k • fourierMode k := by
  classical
  unfold bandMultiplier
  simp_rw [fourierCoeff_fourierMode, mul_ite, mul_one, mul_zero, ite_smul, zero_smul]
  rw [Finset.sum_ite_eq' S k]
  simp [hk]

/-- **Quadratic-form identity.**
`⟪f, M_σ f⟫ = ∑_{n∈S} σ n |f̂ n|²`. -/
theorem inner_bandMultiplier_self (σ : ℤ → ℂ) (S : Finset ℤ) (f : L2Circle T) :
    ⟪f, bandMultiplier σ S f⟫_ℂ = ∑ n ∈ S, σ n * ((‖fourierCoeff f n‖ ^ 2 : ℝ) : ℂ) := by
  unfold bandMultiplier
  rw [inner_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [inner_smul_right, ← inner_conj_symm, inner_fourierMode_eq_fourierCoeff]
  rw [mul_assoc, RCLike.mul_conj]
  norm_cast

/-- **Coercivity from a symbol bound.**  If `Re σ n ≤ -γ` on the band, then
`Re ⟪f, M_σ f⟫ ≤ -γ ‖P_S f‖²`. -/
theorem re_inner_bandMultiplier_le (σ : ℤ → ℂ) (S : Finset ℤ) (f : L2Circle T) (γ : ℝ)
    (hσ : ∀ n ∈ S, (σ n).re ≤ -γ) :
    (⟪f, bandMultiplier σ S f⟫_ℂ).re ≤ -γ * ‖spectralProjection S f‖ ^ 2 := by
  rw [inner_bandMultiplier_self, norm_sq_spectralProjection, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun n hn => ?_
  rw [Complex.re_mul_ofReal]
  exact mul_le_mul_of_nonneg_right (hσ n hn) (sq_nonneg _)

/-- Norm of the multiplied function, by finite Parseval. -/
theorem norm_sq_bandMultiplier (σ : ℤ → ℂ) (S : Finset ℤ) (f : L2Circle T) :
    ‖bandMultiplier σ S f‖ ^ 2 = ∑ n ∈ S, ‖σ n‖ ^ 2 * ‖fourierCoeff f n‖ ^ 2 := by
  have h := (fourierMode_orthonormal (T := T)).inner_sum
    (fun n => σ n * fourierCoeff f n) (fun n => σ n * fourierCoeff f n) S
  have hre := congrArg RCLike.re h
  rw [← @norm_sq_eq_re_inner ℂ] at hre
  unfold bandMultiplier
  rw [hre, map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re, norm_mul, mul_pow]

/-- **Bounded symbol, bounded multiplier.**  If `|σ n| ≤ B` on the band then
`‖M_σ f‖ ≤ B ‖P_S f‖`. -/
theorem norm_bandMultiplier_le (σ : ℤ → ℂ) (S : Finset ℤ) (f : L2Circle T) {B : ℝ}
    (hB0 : 0 ≤ B) (hσ : ∀ n ∈ S, ‖σ n‖ ≤ B) :
    ‖bandMultiplier σ S f‖ ≤ B * ‖spectralProjection S f‖ := by
  have h2 : ‖bandMultiplier σ S f‖ ^ 2 ≤ (B * ‖spectralProjection S f‖) ^ 2 := by
    rw [norm_sq_bandMultiplier, mul_pow, norm_sq_spectralProjection, Finset.mul_sum]
    refine Finset.sum_le_sum fun n hn => ?_
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) (hσ n hn) 2) (sq_nonneg _)
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hB0 (norm_nonneg _))).mp h2

/-! ### Bridge to the maintained scalar WCT symbols

On the circle of circumference `T`, the mode `e_n` has wavenumber
`k_n = 2π n / T`.  The scalar symbols of `Models/BandPass.lean` therefore
define band-limited multipliers, and their pointwise sign bounds become
genuine `L²` energy bounds. -/

/-- Wavenumber of the Fourier mode `e_n` on the circle of circumference `T`. -/
def circleWavenumber (T : ℝ) (n : ℤ) : ℝ :=
  2 * Real.pi * n / T

/-- M3/M7 Swift–Hohenberg linear multiplier on a band. -/
def swiftHohenbergMultiplier (mu b kStar : ℝ) (S : Finset ℤ) (f : L2Circle T) : L2Circle T :=
  bandMultiplier (fun n => (swiftHohenbergLinearSymbol mu b (circleWavenumber T n) kStar : ℂ)) S f

/-- **Function-space growth bound for the M3/M7 linear operator.**  With a
nonnegative fourth-order coefficient, the band-limited Swift–Hohenberg
multiplier has quadratic form at most `mu ‖P_S f‖²`. -/
theorem swiftHohenbergMultiplier_energy_le (mu b kStar : ℝ) (hb : 0 ≤ b) (S : Finset ℤ)
    (f : L2Circle T) :
    (⟪f, swiftHohenbergMultiplier mu b kStar S f⟫_ℂ).re ≤ mu * ‖spectralProjection S f‖ ^ 2 := by
  have h := re_inner_bandMultiplier_le
    (fun n => (swiftHohenbergLinearSymbol mu b (circleWavenumber T n) kStar : ℂ)) S f (-mu)
    (fun n _ => by
      rw [Complex.ofReal_re, neg_neg]
      exact swiftHohenbergLinearSymbol_le_mu mu b _ kStar hb)
  rw [neg_neg] at h
  exact h

/-- E12/E64 quartic growth multiplier on a band. -/
def quarticGrowthMultiplier (r a b : ℝ) (S : Finset ℤ) (f : L2Circle T) : L2Circle T :=
  bandMultiplier (fun n => (quarticGrowthSymbol r a b (circleWavenumber T n) : ℂ)) S f

/-- **Function-space growth bound for the E12 quartic operator.**  For
`b > 0` the band-limited quartic growth multiplier has quadratic form at most
`(r + a²/(4b)) ‖P_S f‖²`, the maximum of the completed square. -/
theorem quarticGrowthMultiplier_energy_le (r a b : ℝ) (hb : 0 < b) (S : Finset ℤ)
    (f : L2Circle T) :
    (⟪f, quarticGrowthMultiplier r a b S f⟫_ℂ).re ≤
      (r + a ^ 2 / (4 * b)) * ‖spectralProjection S f‖ ^ 2 := by
  have h := re_inner_bandMultiplier_le
    (fun n => (quarticGrowthSymbol r a b (circleWavenumber T n) : ℂ)) S f
    (-(r + a ^ 2 / (4 * b)))
    (fun n _ => by
      rw [Complex.ofReal_re, neg_neg,
        quarticGrowthSymbol_completedSquare r a b _ (ne_of_gt hb)]
      have : 0 ≤ b * ((circleWavenumber T n) ^ 2 - a / (2 * b)) ^ 2 :=
        mul_nonneg hb.le (sq_nonneg _)
      linarith)
  rw [neg_neg] at h
  exact h

end FourierSpectral

end

end WCTLean
