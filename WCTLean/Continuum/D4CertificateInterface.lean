import WCTLean.Continuum.CubicQuinticWholeSpace
import WCTLean.Continuum.RadiiPolynomial

/-!
# Periodic D4 certificate: kernel-checked components and exact interface (#21)

Source: `wct-pde` commit `e9a2b589243cfc8fa1492b67a02949c9ba660e93`,
`docs/evidence/d4_production_recovery/continuum_ci/d4_wiener_k20_v2/certificate.json`
(cutoff `K = 20`, low block dimension 232, candidate half-width 70,
Arb precision 128, status PASS), and `docs/D4_WIENER_EXISTENCE_ARGUMENT.md`.

The certificate works on the real D4-invariant Wiener algebra on the torus
`ℝ²/(42ℤ)²` with the bordered map
`F(u, ω) = ((Δ+1)²u − βu³ + γu⁵ − ωu, (42² Σ c_k² − m)/2)` and the
approximate inverse `A` equal to an Arb-midpoint matrix `B` on the low block
`max(|k₁|,|k₂|) ≤ K` and to `1/d_k` on every high mode, where
`d_k = (1 − (2π/42)²|k|²)² − ω̄`.

**Kernel-checked here.**

1. Exact parameter identity: the certificate's binary64 `β = γ` and target
   mass are *exactly* `frozenBeta` and `frozenMass` used by every whole-plane
   theorem (`cert_beta_eq_frozen`, `cert_mass_eq_frozen`), and the exact
   certificate frequency `ω̄` is recorded as a rational.
2. **High-mode diagonal bound** (`d4_high_mode_diagonal_ge`): for every
   integer mode with `max(|k₁|,|k₂|) ≥ 21`, `d_k ≥ 79`, using only Mathlib's
   rigorous `π > 3.141592`. This proves the certificate's
   `high_diagonal_lower ≈ 79.0304` is at least `79` and hence that `A` is
   well-defined and bounded by `1/79` on the entire infinite high block.
3. The certificate's scalar contraction inequalities hold for its reported
   outward upper bounds (`d4_cert_scalar_conditions`).

**Not kernel-checked (computational obstruction).** The bounds `Y0`
(an exact quintic convolution of a ~20 000-mode dyadic candidate, ≈10⁹
high-precision multiplications), `Z0` (needs `‖I − B J_LL‖₁` for a dense
232×232 matrix, ≈10⁷ operations, plus convolution column sums) and `L` are
far beyond Lean kernel reduction; `native_decide` would add the
`Lean.ofReduceBool` trust axiom, which this project excludes.
`d4_conditional_existence` therefore states existence *conditional on* those
three external Arb bounds, and is not counted as a verified certificate.
-/

namespace WCTLean.Continuum

/-! ## 1. Exact certificate parameters -/

/-- Certificate `β = γ = 0x1.05f1d178c75ebp+2`. -/
noncomputable def certBeta : ℝ := (0x105f1d178c75eb : ℝ) / 2 ^ 50

/-- Certificate target mass `0x1.45b8a0bad2714p+1`. -/
noncomputable def certMass : ℝ := (0x145b8a0bad2714 : ℝ) / 2 ^ 51

/-- Certificate frequency `ω̄ = −0x1.712bc3b876ea0p-2`. -/
noncomputable def certOmega : ℝ := -(202953878944629 : ℝ) / 562949953421312

theorem cert_beta_eq_frozen : certBeta = frozenBeta := by
  norm_num [certBeta, frozenBeta]

theorem cert_mass_eq_frozen : certMass = frozenMass := by
  norm_num [certMass, frozenMass]

/-! ## 2. The infinite high-mode block -/

/-- Diagonal of the linearized bordered operator on the 42-torus at mode `k`. -/
noncomputable def d4Diag (k₁ k₂ : ℤ) : ℝ :=
  (1 - (2 * Real.pi / 42) ^ 2 * ((k₁ : ℝ) ^ 2 + (k₂ : ℝ) ^ 2)) ^ 2 - certOmega

theorem sq_ge_441_of_high {k₁ k₂ : ℤ} (hk : 21 ≤ max |k₁| |k₂|) :
    (441 : ℝ) ≤ (k₁ : ℝ) ^ 2 + (k₂ : ℝ) ^ 2 := by
  have h : (441 : ℤ) ≤ k₁ ^ 2 + k₂ ^ 2 := by
    rcases le_max_iff.mp hk with h1 | h1
    · have : (21 : ℤ) ^ 2 ≤ |k₁| ^ 2 := pow_le_pow_left₀ (by norm_num) h1 2
      rw [sq_abs] at this; nlinarith [sq_nonneg k₂]
    · have : (21 : ℤ) ^ 2 ≤ |k₂| ^ 2 := pow_le_pow_left₀ (by norm_num) h1 2
      rw [sq_abs] at this; nlinarith [sq_nonneg k₁]
  exact_mod_cast h

/-- **High-mode diagonal bound.** Every Fourier mode outside the low block
`max(|k₁|,|k₂|) ≤ 20` has `d_k ≥ 79`. -/
theorem d4_high_mode_diagonal_ge {k₁ k₂ : ℤ} (hk : 21 ≤ max |k₁| |k₂|) :
    79 ≤ d4Diag k₁ k₂ := by
  unfold d4Diag certOmega
  have hn := sq_ge_441_of_high hk
  have hpi := Real.pi_gt_d6
  set n : ℝ := (k₁ : ℝ) ^ 2 + (k₂ : ℝ) ^ 2
  have hx : Real.pi ^ 2 ≤ (2 * Real.pi / 42) ^ 2 * n := by
    have : (2 * Real.pi / 42) ^ 2 * 441 = Real.pi ^ 2 := by ring
    rw [← this]
    exact mul_le_mul_of_nonneg_left hn (sq_nonneg _)
  have hpi2 : (3.141592 : ℝ) ^ 2 < Real.pi ^ 2 := by
    exact pow_lt_pow_left₀ hpi (by norm_num) two_ne_zero
  have hlow : (3.141592 : ℝ) ^ 2 - 1 ≤ (2 * Real.pi / 42) ^ 2 * n - 1 := by linarith
  have hpos : 0 ≤ (3.141592 : ℝ) ^ 2 - 1 := by norm_num
  have hsq : ((3.141592 : ℝ) ^ 2 - 1) ^ 2 ≤ (1 - (2 * Real.pi / 42) ^ 2 * n) ^ 2 := by
    rw [show (1 - (2 * Real.pi / 42) ^ 2 * n) ^ 2 = ((2 * Real.pi / 42) ^ 2 * n - 1) ^ 2 by ring]
    exact pow_le_pow_left₀ hpos hlow 2
  norm_num at hsq ⊢
  linarith

/-- The approximate inverse is bounded by `1/79` on every high mode. -/
theorem d4_high_mode_inverse_le {k₁ k₂ : ℤ} (hk : 21 ≤ max |k₁| |k₂|) :
    0 < d4Diag k₁ k₂ ∧ 1 / d4Diag k₁ k₂ ≤ 1 / 79 := by
  have h := d4_high_mode_diagonal_ge hk
  exact ⟨by linarith, one_div_le_one_div_of_le (by norm_num) h⟩

/-! ## 3. Certificate scalar inequalities and conditional existence -/

/-- Outward upper bounds reported by the Arb certificate (radius `r = 10⁻⁸`). -/
noncomputable def certY0Upper : ℝ := 2.3987e-13
noncomputable def certZ0Upper : ℝ := 0.903774
noncomputable def certLUpper : ℝ := 1401.11
noncomputable def certRadius : ℝ := 1e-8

/-- The radii-polynomial inequalities hold for the reported bounds. -/
theorem d4_cert_scalar_conditions :
    certY0Upper + certZ0Upper * certRadius + certLUpper / 2 * certRadius ^ 2 ≤ certRadius ∧
      certZ0Upper + certLUpper * certRadius < 1 := by
  norm_num [certY0Upper, certZ0Upper, certLUpper, certRadius]

/-- **Conditional existence (not a verified certificate).** If the bordered
Newton map `T` on a real Banach space satisfies the three Arb-certified bounds
with the reported constants, it has exactly one fixed point within `10⁻⁸`
of the candidate. The hypotheses `hY0`, `hbound` are the externally computed
inputs that are *not* kernel-checked. -/
theorem d4_conditional_existence {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {T : E → E} {T' : E → E →L[ℝ] E} {xbar : E}
    (hderiv : ∀ x ∈ Metric.closedBall xbar certRadius, HasFDerivAt T (T' x) x)
    (hbound : ∀ x ∈ Metric.closedBall xbar certRadius,
      ‖T' x‖ ≤ certZ0Upper + certLUpper * ‖x - xbar‖)
    (hY0 : ‖T xbar - xbar‖ ≤ certY0Upper) :
    ∃! x, x ∈ Metric.closedBall xbar certRadius ∧ T x = x :=
  radii_polynomial_unique_fixed_point (by norm_num [certRadius])
    (by norm_num [certZ0Upper]) (by norm_num [certLUpper]) hderiv hbound hY0
    d4_cert_scalar_conditions.1 d4_cert_scalar_conditions.2

end WCTLean.Continuum

#print axioms WCTLean.Continuum.cert_beta_eq_frozen
#print axioms WCTLean.Continuum.cert_mass_eq_frozen
#print axioms WCTLean.Continuum.d4_high_mode_diagonal_ge
#print axioms WCTLean.Continuum.d4_high_mode_inverse_le
#print axioms WCTLean.Continuum.d4_cert_scalar_conditions
#print axioms WCTLean.Continuum.d4_conditional_existence
