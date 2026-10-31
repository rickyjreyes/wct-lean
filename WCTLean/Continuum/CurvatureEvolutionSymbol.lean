import WCTLean.Models.ComplexCurvature
import MathProofs.CurvatureUniformBound

/-!
# Frozen-coefficient principal symbols of the canonical curvature evolutions

Issue #19 asks for well-posedness of the *canonical* corrected-curvature
evolution. The analytical registry (`geometry_of_resonance`,
`WCT_FULL_EQUATION_LIST_CORRECTED.md`) contains two distinct candidate
evolutions involving `Θ_ε[ψ] = -(Δψ) R_ε(ψ)`,
`R_ε(ψ) = conj ψ / (|ψ|² + ε² exp(-2α|ψ|²))`:

* **M7** `∂ₜψ = N_curv[ψ] + g|ψ|²ψ + c₁(Δ+σ²)ψ - c₂(Δ+k⋆²)²ψ + …`, `c₂ > 0`,
  with `N_curv[ψ] = Θ_ε[ψ]` (M6B);
* **CM1** `i∂ₜψ = -Θ_ε[ψ] J[ψ]`, `J[ψ] = ε_vac |ψ|² Δψ`.

This module proves the exact frozen-coefficient principal-symbol
dichotomy between them:

1. `R_ε` is **uniformly bounded** over all complex field values
   (reusing the pinned `ReyesMath.positive_curvature_weight_uniform_bound`).
2. Consequently the M7 frozen principal symbol is **uniformly parabolic**:
   `Re p(q) ≤ C - (c₂/2) q²` for every background value and every
   frequency, with an explicit constant independent of the background.
3. CM1 is quadratic in `Δψ`. Its frozen linearized principal coefficient
   `κ = 2 ε_vac |a|² R_ε(a) b` (`a = ψ₀(x₀)`, `b = Δψ₀(x₀)`) vanishes at
   harmonic backgrounds and at nodes, and for every `ε_vac ≠ 0` there are
   backgrounds with `Im κ < 0` **and** backgrounds with `Im κ > 0`. The
   frozen Fourier modes then grow at rate `-Im κ · q`, unbounded in `q`:
   a Hadamard obstruction in either time direction.

Scope. These are statements about frozen-coefficient principal symbols,
the standard necessary condition for well-posedness of the linearization.
They are not a nonlinear local well-posedness theorem for M7 (the Duhamel
fixed point in `C([0,T]; H^s)` is not formalized here), and they are not by
themselves a proof that the nonlinear CM1 Cauchy problem is ill-posed.
The extra M7 terms `c₄R^{-(2+n/p)}ψ` and `ηψ∘ξ(t)` are not specified
precisely enough in the registry to be included.
-/

namespace WCTLean.Continuum

open WCTLean

/-! ## 1. Uniform bound on the corrected reciprocal -/

/-- The explicit uniform bound constant, from the pinned weight bound. -/
noncomputable def curvatureReciprocalBound (ε α : ℝ) : ℝ :=
  1 + (ε ^ 2 * Real.exp (-2 * α))⁻¹ ^ 2

theorem curvatureReciprocalBound_ge_one (ε α : ℝ) :
    1 ≤ curvatureReciprocalBound ε α := by
  unfold curvatureReciprocalBound
  have := sq_nonneg (ε ^ 2 * Real.exp (-2 * α))⁻¹
  linarith

/-- `‖R_ε(ψ)‖²` is exactly the pinned positive curvature weight at
density `|ψ|²`. -/
theorem norm_sq_complexRegularizedReciprocal
    (ψ : ℂ) (ε α : ℝ) (hε : 0 < ε) :
    ‖complexRegularizedReciprocal ψ ε α‖ ^ 2 =
      ReyesMath.positiveCurvatureWeight ε α (Complex.normSq ψ) := by
  have hD := complexRegularizerDenominator_positive ψ ε α hε
  unfold complexRegularizedReciprocal
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hD.le, div_pow,
    norm_star, ← Complex.normSq_eq_norm_sq]
  unfold ReyesMath.positiveCurvatureWeight complexRegularizerDenominator
  rfl

/-- **Uniform bound.** For `ε > 0`, `α ≥ 0`, the corrected reciprocal is
bounded over every complex field value, including nodes and large fields. -/
theorem complexRegularizedReciprocal_uniform_bound
    (ψ : ℂ) (ε α : ℝ) (hε : 0 < ε) (hα : 0 ≤ α) :
    ‖complexRegularizedReciprocal ψ ε α‖ ≤ curvatureReciprocalBound ε α := by
  set n := ‖complexRegularizedReciprocal ψ ε α‖
  have hsq : n ^ 2 ≤ curvatureReciprocalBound ε α := by
    rw [norm_sq_complexRegularizedReciprocal ψ ε α hε]
    exact ReyesMath.positive_curvature_weight_uniform_bound ε α _ hε hα
      (Complex.normSq_nonneg ψ)
  have h1 := curvatureReciprocalBound_ge_one ε α
  by_cases hn : n ≤ 1
  · linarith
  · push_neg at hn
    nlinarith

/-! ## 2. M7: uniform parabolicity of the frozen principal symbol -/

/-- Frozen-coefficient principal symbol of the linearized M7 operator at a
background value `ψ₀`, evaluated on a Fourier mode with `|ξ|² = q`
(`Δ ↦ -q`). The curvature term contributes `-(Δh) R_ε(ψ₀) ↦ q R_ε(ψ₀)`;
the zeroth-order term `-(Δψ₀) DR_ε(ψ₀)[h]` and the cubic term are lower
order and are not part of the principal symbol. -/
noncomputable def m7PrincipalSymbol
    (c₁ c₂ σ kstar ε α : ℝ) (ψ₀ : ℂ) (q : ℝ) : ℂ :=
  ((c₁ * (σ ^ 2 - q) - c₂ * (kstar ^ 2 - q) ^ 2 : ℝ) : ℂ) +
    (q : ℂ) * complexRegularizedReciprocal ψ₀ ε α

/-- The explicit background-independent parabolicity constant. -/
noncomputable def m7ParabolicConstant (c₁ c₂ σ kstar ε α : ℝ) : ℝ :=
  c₁ * σ ^ 2 +
    (curvatureReciprocalBound ε α + |c₁| + 2 * c₂ * kstar ^ 2) ^ 2 / (2 * c₂)

/-- **M7 frozen principal symbol is uniformly parabolic.** For `c₂ > 0`,
`ε > 0`, `α ≥ 0`, every background value `ψ₀`, and every `q ≥ 0`,
`Re p(q) ≤ C - (c₂/2) q²` with `C` independent of `ψ₀` and `q`.
The fourth-order damping strictly dominates the bounded curvature
quotient; no uniform ellipticity of the quotient itself is used. -/
theorem m7_principal_symbol_uniformly_parabolic
    (c₁ c₂ σ kstar ε α : ℝ) (hc₂ : 0 < c₂) (hε : 0 < ε) (hα : 0 ≤ α)
    (ψ₀ : ℂ) {q : ℝ} (hq : 0 ≤ q) :
    (m7PrincipalSymbol c₁ c₂ σ kstar ε α ψ₀ q).re ≤
      m7ParabolicConstant c₁ c₂ σ kstar ε α - c₂ / 2 * q ^ 2 := by
  set B := curvatureReciprocalBound ε α
  set R := complexRegularizedReciprocal ψ₀ ε α
  have hB : ‖R‖ ≤ B := complexRegularizedReciprocal_uniform_bound ψ₀ ε α hε hα
  have hRe : ((q : ℂ) * R).re ≤ q * B := by
    have h1 : ((q : ℂ) * R).re = q * R.re := by simp
    rw [h1]
    exact mul_le_mul_of_nonneg_left ((Complex.re_le_norm R).trans hB) hq
  have hsym : (m7PrincipalSymbol c₁ c₂ σ kstar ε α ψ₀ q).re =
      c₁ * (σ ^ 2 - q) - c₂ * (kstar ^ 2 - q) ^ 2 + ((q : ℂ) * R).re := by
    simp only [m7PrincipalSymbol, Complex.add_re, Complex.ofReal_re, R]
  rw [hsym]
  set M := B + |c₁| + 2 * c₂ * kstar ^ 2
  have hc1 : -(c₁ * q) ≤ |c₁| * q := by
    have := neg_abs_le c₁
    nlinarith [abs_nonneg c₁]
  have hk4 : 0 ≤ c₂ * kstar ^ 4 := by positivity
  -- Young: M q ≤ (c₂/2) q² + M²/(2 c₂).
  have hyoung : M * q ≤ c₂ / 2 * q ^ 2 + M ^ 2 / (2 * c₂) := by
    have hsq : 0 ≤ (c₂ * q - M) ^ 2 / (2 * c₂) := by positivity
    have hexp : (c₂ * q - M) ^ 2 / (2 * c₂) =
        c₂ / 2 * q ^ 2 - M * q + M ^ 2 / (2 * c₂) := by
      field_simp
      ring
    linarith
  unfold m7ParabolicConstant
  change _ ≤ c₁ * σ ^ 2 + M ^ 2 / (2 * c₂) - c₂ / 2 * q ^ 2
  nlinarith

/-- The parabolic bound forces the frozen M7 growth rate to `-∞` at high
frequency: above any threshold there is a frequency beyond which every
frozen mode, at every background value, decays faster than that rate. -/
theorem m7_principal_symbol_high_frequency_damping
    (c₁ c₂ σ kstar ε α : ℝ) (hc₂ : 0 < c₂) (hε : 0 < ε) (hα : 0 ≤ α)
    (Λ : ℝ) :
    ∃ Q : ℝ, ∀ q ≥ Q, ∀ ψ₀ : ℂ,
      (m7PrincipalSymbol c₁ c₂ σ kstar ε α ψ₀ q).re ≤ -Λ := by
  set C := m7ParabolicConstant c₁ c₂ σ kstar ε α
  refine ⟨max 1 (2 * (|C| + |Λ|) / c₂ + 1), ?_⟩
  intro q hq ψ₀
  have hq1 : 1 ≤ q := (le_max_left _ _).trans hq
  have hq2 : 2 * (|C| + |Λ|) / c₂ + 1 ≤ q := (le_max_right _ _).trans hq
  have hmain := m7_principal_symbol_uniformly_parabolic c₁ c₂ σ kstar ε α
    hc₂ hε hα ψ₀ (by linarith : (0 : ℝ) ≤ q)
  have hbig : 2 * (|C| + |Λ|) / c₂ ≤ q := by linarith
  have hbig' : 2 * (|C| + |Λ|) ≤ c₂ * q := by
    rw [div_le_iff₀ hc₂] at hbig; linarith
  have hqq : q ≤ q ^ 2 := by nlinarith
  have hC : C ≤ |C| := le_abs_self C
  have hΛ : Λ ≤ |Λ| := le_abs_self Λ
  have : c₂ / 2 * q ^ 2 ≥ |C| + |Λ| := by nlinarith
  linarith

/-! ## 3. CM1: degenerate and sign-indefinite frozen principal coefficient -/

/-- The CM1 right-hand side `-Θ_ε[ψ] J[ψ]` as a function of the
pointwise field value `ψ` and Laplacian value `lap = Δψ`,
with `J = ε_vac |ψ|² Δψ`. The CM1 equation is `i ∂ₜψ = cm1Rhs`. -/
noncomputable def cm1Rhs (lap ψ : ℂ) (ε α εvac : ℝ) : ℂ :=
  -(thetaComplex lap ψ ε α) * ((εvac : ℂ) * (Complex.normSq ψ : ℂ) * lap)

/-- CM1 is exactly quadratic in the Laplacian: `ε_vac |ψ|² R_ε(ψ) (Δψ)²`. -/
theorem cm1Rhs_quadratic_in_laplacian (lap ψ : ℂ) (ε α εvac : ℝ) :
    cm1Rhs lap ψ ε α εvac =
      (εvac : ℂ) * (Complex.normSq ψ : ℂ) *
        complexRegularizedReciprocal ψ ε α * lap ^ 2 := by
  unfold cm1Rhs thetaComplex
  ring

/-- Principal (second-derivative) coefficient of the CM1 linearization at a
background with field value `a` and Laplacian value `b`. -/
noncomputable def cm1PrincipalCoefficient (a b : ℂ) (ε α εvac : ℝ) : ℂ :=
  2 * (εvac : ℂ) * (Complex.normSq a : ℂ) *
    complexRegularizedReciprocal a ε α * b

/-- Exact Taylor expansion in the second-order slot: perturbing `Δψ` by `d`
changes the CM1 right-hand side by `κ d` plus an explicit quadratic term. -/
theorem cm1Rhs_laplacian_expansion (a b d : ℂ) (ε α εvac : ℝ) :
    cm1Rhs (b + d) a ε α εvac - cm1Rhs b a ε α εvac =
      cm1PrincipalCoefficient a b ε α εvac * d +
        (εvac : ℂ) * (Complex.normSq a : ℂ) *
          complexRegularizedReciprocal a ε α * d ^ 2 := by
  rw [cm1Rhs_quadratic_in_laplacian, cm1Rhs_quadratic_in_laplacian]
  unfold cm1PrincipalCoefficient
  ring

/-- **Total degeneracy at harmonic backgrounds**: where `Δψ₀ = 0`, the CM1
linearization has no second-order part at all. -/
theorem cm1_principal_coefficient_harmonic (a : ℂ) (ε α εvac : ℝ) :
    cm1PrincipalCoefficient a 0 ε α εvac = 0 := by
  simp [cm1PrincipalCoefficient]

/-- **Total degeneracy at nodes**. -/
theorem cm1_principal_coefficient_node (b : ℂ) (ε α εvac : ℝ) :
    cm1PrincipalCoefficient 0 b ε α εvac = 0 := by
  simp [cm1PrincipalCoefficient]

/-- Exact imaginary part of the CM1 principal coefficient. -/
theorem cm1_principal_coefficient_im (a b : ℂ) (ε α εvac : ℝ) :
    (cm1PrincipalCoefficient a b ε α εvac).im =
      2 * εvac * Complex.normSq a *
        (star a * b).im / complexRegularizerDenominator a ε α := by
  unfold cm1PrincipalCoefficient complexRegularizedReciprocal
  set D := complexRegularizerDenominator a ε α
  have hrw : 2 * (εvac : ℂ) * (Complex.normSq a : ℂ) * (star a / (D : ℂ)) * b =
      ((2 * εvac * Complex.normSq a / D : ℝ) : ℂ) * (star a * b) := by
    push_cast
    ring
  rw [hrw, Complex.im_ofReal_mul]
  ring

/-- Growth rate of the frozen Fourier mode `h = e^{λt + iξ·x}`, `|ξ|² = q`,
for `i ∂ₜh = κ Δh`: the dispersion relation is `i λ = -κ q`, i.e.
`λ = i κ q`. -/
noncomputable def frozenModeExponent (κ : ℂ) (q : ℝ) : ℂ :=
  Complex.I * κ * q

theorem frozenModeExponent_dispersion (κ : ℂ) (q : ℝ) :
    Complex.I * frozenModeExponent κ q = -(κ * q) := by
  unfold frozenModeExponent
  rw [← mul_assoc, ← mul_assoc, Complex.I_mul_I]
  ring

theorem frozenModeExponent_re (κ : ℂ) (q : ℝ) :
    (frozenModeExponent κ q).re = -κ.im * q := by
  simp [frozenModeExponent]

/-- If `Im κ < 0`, frozen-mode amplification over any positive time is
unbounded over frequencies: no estimate `‖h(t)‖ ≤ C ‖h(0)‖` can hold in
any Sobolev norm (mode amplitudes grow like `exp(|Im κ| q t)`, beating any
polynomial weight). -/
theorem frozen_mode_unbounded_growth
    (κ : ℂ) (hκ : κ.im < 0) (C t : ℝ) (ht : 0 < t) :
    ∃ q : ℝ, 0 ≤ q ∧ C < Real.exp ((frozenModeExponent κ q).re * t) := by
  set g : ℝ := -κ.im with hg
  have hgpos : 0 < g := by linarith
  refine ⟨(|C| + 1) / (g * t), by positivity, ?_⟩
  rw [frozenModeExponent_re]
  have hcalc : -κ.im * ((|C| + 1) / (g * t)) * t = |C| + 1 := by
    rw [← hg]; field_simp
  rw [hcalc]
  have h1 : |C| + 1 + 1 ≤ Real.exp (|C| + 1) := Real.add_one_le_exp _
  have h2 : C ≤ |C| := le_abs_self C
  linarith

/-- **CM1 frozen-coefficient Hadamard obstruction.** For every `ε > 0`,
`α`, and every nonzero coupling `ε_vac`, there are pointwise backgrounds
`(a, b) = (ψ₀(x₀), Δψ₀(x₀))` whose frozen CM1 linearization has
unbounded forward-time mode growth, and others with unbounded
backward-time growth. Hence neither time orientation (nor sign of
`ε_vac`) makes all frozen problems well-posed. -/
theorem cm1_frozen_hadamard_obstruction
    (ε α εvac : ℝ) (hε : 0 < ε) (hvac : εvac ≠ 0) :
    (∃ a b : ℂ, (cm1PrincipalCoefficient a b ε α εvac).im < 0 ∧
      ∀ C t : ℝ, 0 < t → ∃ q : ℝ, 0 ≤ q ∧
        C < Real.exp
          ((frozenModeExponent (cm1PrincipalCoefficient a b ε α εvac) q).re * t)) ∧
    (∃ a b : ℂ, 0 < (cm1PrincipalCoefficient a b ε α εvac).im ∧
      ∀ C t : ℝ, 0 < t → ∃ q : ℝ, 0 ≤ q ∧
        C < Real.exp
          ((frozenModeExponent (cm1PrincipalCoefficient a b ε α εvac) q).re * (-t))) := by
  have hD : 0 < complexRegularizerDenominator 1 ε α :=
    complexRegularizerDenominator_positive 1 ε α hε
  have hv2 : 0 < εvac ^ 2 := by positivity
  have himneg : (cm1PrincipalCoefficient 1 (-(Complex.I * εvac)) ε α εvac).im < 0 := by
    rw [cm1_principal_coefficient_im]
    have : (star (1 : ℂ) * -(Complex.I * εvac)).im = -εvac := by simp
    rw [this]
    simp only [Complex.normSq_one, mul_one]
    have : 2 * εvac * -εvac / complexRegularizerDenominator 1 ε α =
        -(2 * εvac ^ 2 / complexRegularizerDenominator 1 ε α) := by ring
    rw [this]
    have : 0 < 2 * εvac ^ 2 / complexRegularizerDenominator 1 ε α := by positivity
    linarith
  have himpos : 0 < (cm1PrincipalCoefficient 1 (Complex.I * εvac) ε α εvac).im := by
    rw [cm1_principal_coefficient_im]
    have : (star (1 : ℂ) * (Complex.I * εvac)).im = εvac := by simp
    rw [this]
    simp only [Complex.normSq_one, mul_one]
    have : 2 * εvac * εvac / complexRegularizerDenominator 1 ε α =
        2 * εvac ^ 2 / complexRegularizerDenominator 1 ε α := by ring
    rw [this]
    positivity
  refine ⟨⟨1, -(Complex.I * εvac), himneg, fun C t ht =>
      frozen_mode_unbounded_growth _ himneg C t ht⟩,
    ⟨1, Complex.I * εvac, himpos, fun C t ht => ?_⟩⟩
  -- Backward time: the mode exponent of `-κ` reproduces forward growth.
  set κ := cm1PrincipalCoefficient 1 (Complex.I * εvac) ε α εvac
  have hneg : (-κ).im < 0 := by simp; linarith
  obtain ⟨q, hq, hgrow⟩ := frozen_mode_unbounded_growth (-κ) hneg C t ht
  refine ⟨q, hq, ?_⟩
  have : (frozenModeExponent κ q).re * -t = (frozenModeExponent (-κ) q).re * t := by
    rw [frozenModeExponent_re, frozenModeExponent_re, Complex.neg_im]
    ring
  rw [this]; exact hgrow

end WCTLean.Continuum

#print axioms WCTLean.Continuum.complexRegularizedReciprocal_uniform_bound
#print axioms WCTLean.Continuum.m7_principal_symbol_uniformly_parabolic
#print axioms WCTLean.Continuum.m7_principal_symbol_high_frequency_damping
#print axioms WCTLean.Continuum.cm1Rhs_laplacian_expansion
#print axioms WCTLean.Continuum.cm1_principal_coefficient_harmonic
#print axioms WCTLean.Continuum.cm1_principal_coefficient_im
#print axioms WCTLean.Continuum.frozen_mode_unbounded_growth
#print axioms WCTLean.Continuum.cm1_frozen_hadamard_obstruction
