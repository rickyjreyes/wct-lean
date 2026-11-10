import Mathlib
import WCTLean.Models.S004PrincipalDegeneracy

/-!
# Exact amplitude-annulus coercivity for the corrected S004 curvature coefficient

The corrected S004 weight
    F(s) = s / (s + epsilon^2 exp(-2 alpha s))^2
does NOT have a globally positive lower bound, even for s>0.

This file proves the sharp qualitative distinction:
* on ANY FIXED amplitude-density annulus delta <= s <= M with delta>0,
  alpha>=0 and epsilon>0, F(s) >= delta/(M+epsilon^2)^2>0;
* at arbitrarily large s>0, F(s) < c for every c>0.

These bounds are for a COEFFICIENT on a specified field sector.
They do not prove that the actual WCT PDE preserves its amplitude
annulus, that its full mixed high-order principal symbol is coercive,
or that any nonlinear flow is well-posed.
-/

namespace WCTLean

/-- The Gaussian-like regularizer factor never exceeds 1 at
nonnegative real squared field amplitude. -/
theorem corrected_exponential_le_one
    (alpha s : ℝ) (ha : 0 ≤ alpha) (hs : 0 ≤ s) :
    Real.exp (-2 * alpha * s) ≤ 1 := by
  apply (Real.exp_le_one_iff).mpr
  nlinarith [mul_nonneg ha hs]

/-- Denominator upper bound when amplitude density lies below M. -/
theorem correctedDenominator_le_upper
    (epsilon alpha s M : ℝ)
    (ha : 0 ≤ alpha) (hs : 0 ≤ s) (hM : s ≤ M) :
    correctedRadialDenominator epsilon alpha s ≤ M + epsilon ^ 2 := by
  have he := corrected_exponential_le_one alpha s ha hs
  have hepssq : 0 ≤ epsilon ^ 2 := sq_nonneg epsilon
  have hmul := mul_le_mul_of_nonneg_left he hepssq
  unfold correctedRadialDenominator
  nlinarith

/-- A strictly positive coefficient floor holds on a genuinely
bounded-away-from-zero AND bounded-above density annulus. -/
theorem curvatureWeight_ge_on_amplitude_annulus
    (epsilon alpha delta M s : ℝ)
    (heps : 0 < epsilon) (ha : 0 ≤ alpha)
    (hdelta : 0 < delta) (hlo : delta ≤ s) (hhi : s ≤ M) :
    delta / (M + epsilon ^ 2) ^ 2 ≤
      correctedRadialWeight epsilon alpha s := by
  have hs : 0 ≤ s := le_trans hdelta.le hlo
  have hM : 0 < M := lt_of_lt_of_le (lt_of_lt_of_le hdelta hlo) hhi
  have hdle :=
    correctedDenominator_le_upper epsilon alpha s M ha hs hhi
  have hdpos : 0 < correctedRadialDenominator epsilon alpha s := by
    unfold correctedRadialDenominator
    have he : 0 ≤ epsilon ^ 2 * Real.exp (-2 * alpha * s) := by positivity
    linarith
  have hupper : 0 < M + epsilon ^ 2 := by positivity
  have hsq :
      (correctedRadialDenominator epsilon alpha s) ^ 2 ≤
        (M + epsilon ^ 2) ^ 2 := by nlinarith
  have h1 := mul_le_mul_of_nonneg_left hsq hdelta.le
  have h2 := mul_le_mul_of_nonneg_right hlo (sq_nonneg (M + epsilon ^ 2))
  have hprod := le_trans h1 h2
  unfold correctedRadialWeight
  apply (div_le_div_iff₀ (sq_pos_of_pos hupper) (sq_pos_of_pos hdpos)).mpr
  nlinarith

/-- The lower bound on the annulus is genuinely strictly positive. -/
theorem curvatureWeight_annulus_floor_positive
    (epsilon delta M : ℝ)
    (heps : 0 < epsilon) (hd : 0 < delta) (hM : 0 < M) :
    0 < delta / (M + epsilon ^ 2) ^ 2 := by
  have hupper : 0 < M + epsilon ^ 2 := by positivity
  exact div_pos hd (sq_pos_of_pos hupper)

/-- Large densities also make the curvature principal weight small:
the denominator is at least s, hence F(s) <= 1/s. -/
theorem correctedWeight_le_inverse_density
    (epsilon alpha s : ℝ) (hs : 0 < s) :
    correctedRadialWeight epsilon alpha s ≤ 1 / s := by
  have he : 0 ≤ epsilon ^ 2 * Real.exp (-2 * alpha * s) := by positivity
  have hdle : s ≤ correctedRadialDenominator epsilon alpha s := by
    unfold correctedRadialDenominator
    linarith
  have hdpos : 0 < correctedRadialDenominator epsilon alpha s :=
    lt_of_lt_of_le hs hdle
  have hsq : s ^ 2 ≤ (correctedRadialDenominator epsilon alpha s) ^ 2 := by
    nlinarith
  unfold correctedRadialWeight
  apply (div_le_div_iff₀ (sq_pos_of_pos hdpos) hs).mpr
  nlinarith

/-- Explicit high-density counterexample to a uniform positive principal
coefficient, independent of epsilon and alpha. -/
theorem arbitrarily_small_weight_high_density
    (epsilon alpha c : ℝ) (hc : 0 < c) :
    ∃ s : ℝ, 0 < s ∧ 1 / c < s ∧
      correctedRadialWeight epsilon alpha s < c := by
  let s : ℝ := 2 / c
  have hs : 0 < s := by dsimp [s]; positivity
  have hsmall := correctedWeight_le_inverse_density epsilon alpha s hs
  have hinv : 1 / s = c / 2 := by
    dsimp [s]
    field_simp
  have hbig : 1 / c < s := by
    dsimp [s]
    apply (div_lt_div_iff₀ hc hc).mpr
    nlinarith
  refine ⟨s, hs, hbig, ?_⟩
  rw [hinv] at hsmall
  linarith

/-! ## Explicit almost-everywhere continuum-field coercivity interface -/

/-- For any measure space and any complex field whose amplitude stays
within the prescribed annulus almost everywhere, the genuine S004
curvature coefficient has the same positive floor almost everywhere.
This is an ACTUAL function-space assertion, not just a canonical jet.
It does not supply an invariant annulus for an evolution. -/
theorem complexWeight_ae_lower_bound
    {Ω : Type*} [MeasurableSpace Ω] (mu : MeasureTheory.Measure Ω)
    (psi : Ω → ℂ)
    (epsilon alpha delta M : ℝ)
    (heps : 0 < epsilon) (ha : 0 ≤ alpha)
    (hdelta : 0 < delta)
    (hpsi : ∀ᵐ x ∂mu,
      delta ≤ Complex.normSq (psi x) ∧ Complex.normSq (psi x) ≤ M) :
    ∀ᵐ x ∂mu,
      delta / (M + epsilon ^ 2) ^ 2 ≤
        Complex.normSq (psi x) /
          (complexRegularizerDenominator (psi x) epsilon alpha) ^ 2 := by
  filter_upwards [hpsi] with x hx
  simpa only [correctedRadialDenominator_eq_complex, correctedRadialWeight] using
    curvatureWeight_ge_on_amplitude_annulus epsilon alpha delta M
      (Complex.normSq (psi x)) heps ha hdelta hx.1 hx.2

/-- Under the same a.e. amplitude hypothesis, the weighted S004
curvature quadratic energy density controls the unweighted density.
No unproved integration, measurability or boundary identity is
assumed; the exact a.e. inequality is available to such theorems. -/
theorem curvatureEnergyDensity_ae_lower_bound
    {Ω : Type*} [MeasurableSpace Ω] (mu : MeasureTheory.Measure Ω)
    (psi Q : Ω → ℂ)
    (epsilon alpha delta M : ℝ)
    (heps : 0 < epsilon) (ha : 0 ≤ alpha)
    (hdelta : 0 < delta)
    (hpsi : ∀ᵐ x ∂mu,
      delta ≤ Complex.normSq (psi x) ∧ Complex.normSq (psi x) ≤ M) :
    ∀ᵐ x ∂mu,
      (delta / (M + epsilon ^ 2) ^ 2) * ‖Q x‖ ^ 2 ≤
        (Complex.normSq (psi x) /
          (complexRegularizerDenominator (psi x) epsilon alpha) ^ 2) *
          ‖Q x‖ ^ 2 := by
  have hfloor := complexWeight_ae_lower_bound mu psi
    epsilon alpha delta M heps ha hdelta hpsi
  filter_upwards [hfloor] with x hx
  exact mul_le_mul_of_nonneg_right hx (sq_nonneg _)

end WCTLean
