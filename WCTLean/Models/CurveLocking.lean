/-
  WCTLean/Models/CurveLocking.lean

  Issue #24: curve-integral locking and winding quantization from the
  geometric (line-integral) formulation.

  Class of curves: `C¹` parametrized loops of nonvanishing complex field
  values, `γ : ℝ → ℂ`, `γ t ≠ 0`, with continuous derivative and closed
  endpoints `γ b = γ a`.  This covers every field `ψ : U → ℂ \ {0}` on an
  open subset `U` of a real normed space `E` (in particular every chart
  domain of a manifold) composed with a `C¹` loop `c : ℝ → U`
  (`field_loop_winding_quantized`).

  * `exp_logCurveIntegral`: `exp (∫_a^b γ'/γ) = γ b / γ a` (no closedness).
  * `winding_quantized`: on a closed loop, `∮ dψ/ψ = 2π i n` for an integer
    `n`; the phase circulation `Im ∮ dψ/ψ` satisfies the E11 predicate
    `WindingQuantized` and the amplitude part `Re ∮ dψ/ψ` vanishes
    (`phaseCirculation_windingQuantized`, `amplitude_return_zero`).
  * Local versus global: if the field has a single-valued `C¹` logarithm
    along the loop the circulation is `0` (`logCurveIntegral_of_global_log`,
    path independence), while `t ↦ e^{int}` has circulation `2πn`
    (`logCurveIntegral_exp_int`), so every integer occurs and nonzero winding
    is a global obstruction to a single-valued phase
    (`no_global_log_of_winding_ne_zero`).  With an explicit polar phase
    `γ = ρ e^{iθ}` the circulation is `θ b - θ a` (`polar_phaseCirculation`,
    a local phase identity).
  * Additivity: `∮ d(ψ₁ψ₂)/(ψ₁ψ₂) = ∮ dψ₁/ψ₁ + ∮ dψ₂/ψ₂`
    (`logCurveIntegral_mul`); the E11 law `windingQuantized_add` is recovered
    geometrically (`product_loop_windingQuantized`).
  * E4 link: a pointwise lock `θ' = σ + α/w` around a loop of winding `n`
    forces `α = alphaLock n (∫σ) (∫1/w)` (`alpha_determined_by_winding`).

  Homotopy invariance and loops on general (non-Euclidean-chart) manifolds
  are not formalized here.
-/

import Mathlib
import WCTLean.Models.PhaseFlux
import WCTLean.Models.Locking

namespace WCTLean

open Complex intervalIntegral

noncomputable section

/-- Curve integral of the logarithmic form `dψ/ψ` along `γ` with velocity `γ'`. -/
def logCurveIntegral (γ γ' : ℝ → ℂ) (a b : ℝ) : ℂ :=
  ∫ t in a..b, γ' t / γ t

/-- Phase circulation `Im ∮ dψ/ψ`. -/
def phaseCirculation (γ γ' : ℝ → ℂ) (a b : ℝ) : ℝ :=
  (logCurveIntegral γ γ' a b).im

/-- `C¹` curve of nonvanishing field values. -/
structure C1NonvanishingCurve (γ γ' : ℝ → ℂ) : Prop where
  hasDeriv : ∀ t, HasDerivAt γ (γ' t) t
  cont : Continuous γ'
  ne : ∀ t, γ t ≠ 0

theorem C1NonvanishingCurve.continuous {γ γ' : ℝ → ℂ} (h : C1NonvanishingCurve γ γ') :
    Continuous γ :=
  continuous_iff_continuousAt.2 fun t => (h.hasDeriv t).continuousAt

theorem C1NonvanishingCurve.continuous_quotient {γ γ' : ℝ → ℂ} (h : C1NonvanishingCurve γ γ') :
    Continuous fun t => γ' t / γ t :=
  h.cont.div h.continuous h.ne

/-- **Exponentiated curve integral.**  `exp (∫_a^b γ'/γ) = γ b / γ a`. -/
theorem exp_logCurveIntegral {γ γ' : ℝ → ℂ} (h : C1NonvanishingCurve γ γ') (a b : ℝ) :
    Complex.exp (logCurveIntegral γ γ' a b) = γ b / γ a := by
  set F : ℝ → ℂ := fun u => ∫ t in a..u, γ' t / γ t with hF_def
  have hF : ∀ u, HasDerivAt F (γ' u / γ u) u := fun u =>
    (h.continuous_quotient.integral_hasStrictDerivAt a u).hasDerivAt
  set G : ℝ → ℂ := fun u => γ u * Complex.exp (-F u) with hG_def
  have hG : ∀ u, HasDerivAt G 0 u := by
    intro u
    have h1 := (h.hasDeriv u).mul (hF u).neg.cexp
    convert h1 using 1
    have hne := h.ne u
    field_simp
    ring
  have hconst : G b = G a :=
    is_const_of_deriv_eq_zero (fun u => (hG u).differentiableAt) (fun u => (hG u).deriv) b a
  simp only [hG_def, hF_def, intervalIntegral.integral_same, neg_zero, Complex.exp_zero,
    mul_one] at hconst
  unfold logCurveIntegral
  have hinv : Complex.exp (-(∫ t in a..b, γ' t / γ t)) =
      (Complex.exp (∫ t in a..b, γ' t / γ t))⁻¹ := Complex.exp_neg _
  rw [hinv] at hconst
  have hexp_ne : Complex.exp (∫ t in a..b, γ' t / γ t) ≠ 0 := Complex.exp_ne_zero _
  have ha := h.ne a
  field_simp at hconst ⊢
  exact hconst.symm

/-- **Winding quantization.**  Around a closed `C¹` loop of nonvanishing field
values, `∮ dψ/ψ = 2π i n` for an integer `n`. -/
theorem winding_quantized {γ γ' : ℝ → ℂ} (h : C1NonvanishingCurve γ γ') {a b : ℝ}
    (hclosed : γ b = γ a) :
    ∃ n : ℤ, logCurveIntegral γ γ' a b = 2 * Real.pi * Complex.I * n := by
  have hexp := exp_logCurveIntegral h a b
  rw [hclosed, div_self (h.ne a)] at hexp
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hexp
  exact ⟨n, by rw [hn]; ring⟩

/-- **E11 from geometry.**  The phase circulation of a closed loop satisfies
the integer winding law `WindingQuantized`. -/
theorem phaseCirculation_windingQuantized {γ γ' : ℝ → ℂ} (h : C1NonvanishingCurve γ γ')
    {a b : ℝ} (hclosed : γ b = γ a) :
    ∃ n : ℤ, WindingQuantized (phaseCirculation γ γ' a b) n := by
  obtain ⟨n, hn⟩ := winding_quantized h hclosed
  refine ⟨n, ?_⟩
  unfold WindingQuantized phaseCirculation
  rw [hn]
  simp

/-- The amplitude part of the logarithmic circulation vanishes on a closed
loop: `Re ∮ dψ/ψ = 0`. -/
theorem amplitude_return_zero {γ γ' : ℝ → ℂ} (h : C1NonvanishingCurve γ γ') {a b : ℝ}
    (hclosed : γ b = γ a) : (logCurveIntegral γ γ' a b).re = 0 := by
  obtain ⟨n, hn⟩ := winding_quantized h hclosed
  rw [hn]
  simp

/-! ### Local phase identities versus global topology -/

/-- **Path independence with a single-valued logarithm.**  If `γ = exp ∘ L`
for a `C¹` function `L`, then `∫_a^b γ'/γ = L b - L a`; in particular the
circulation vanishes when `L` is single valued around the loop. -/
theorem logCurveIntegral_of_global_log (L L' : ℝ → ℂ) (hL : ∀ t, HasDerivAt L (L' t) t)
    (hL' : Continuous L') (a b : ℝ) :
    logCurveIntegral (fun t => Complex.exp (L t)) (fun t => Complex.exp (L t) * L' t) a b =
      L b - L a := by
  unfold logCurveIntegral
  have hpt : ∀ t, Complex.exp (L t) * L' t / Complex.exp (L t) = L' t := by
    intro t; field_simp [Complex.exp_ne_zero]
  simp_rw [hpt]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hL t)
    (hL'.intervalIntegrable _ _)

/-- **Every integer occurs.**  The loop `t ↦ e^{int}` on `[0, 2π]` has
logarithmic circulation `2π i n`. -/
theorem logCurveIntegral_exp_int (n : ℤ) :
    logCurveIntegral (fun t => Complex.exp (Complex.I * n * t))
        (fun t => Complex.exp (Complex.I * n * t) * (Complex.I * n)) 0 (2 * Real.pi) =
      2 * Real.pi * Complex.I * n := by
  have hL : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Complex.I * n * (t : ℂ)) (Complex.I * n) t := by
    intro t
    have := (hasDerivAt_id (t : ℝ)).ofReal_comp.const_mul (Complex.I * n)
    simpa using this
  rw [logCurveIntegral_of_global_log (fun t : ℝ => Complex.I * n * t) (fun _ => Complex.I * n) hL
    continuous_const]
  push_cast
  ring

/-- The loop `t ↦ e^{int}` is a closed `C¹` nonvanishing curve on `[0, 2π]`. -/
theorem exp_int_loop_closed (n : ℤ) :
    C1NonvanishingCurve (fun t => Complex.exp (Complex.I * n * t))
        (fun t => Complex.exp (Complex.I * n * t) * (Complex.I * n)) ∧
      Complex.exp (Complex.I * n * ((2 * Real.pi : ℝ) : ℂ)) =
        Complex.exp (Complex.I * n * ((0 : ℝ) : ℂ)) := by
  refine ⟨⟨fun t => ?_, by fun_prop, fun t => Complex.exp_ne_zero _⟩, ?_⟩
  · have h := ((hasDerivAt_id (t : ℝ)).ofReal_comp.const_mul (Complex.I * n)).cexp
    simpa using h
  · rw [Complex.ofReal_zero, mul_zero, Complex.exp_zero, Complex.exp_eq_one_iff]
    exact ⟨n, by push_cast; ring⟩

/-- A single-valued `C¹` logarithm along the loop forces zero circulation. -/
theorem logCurveIntegral_eq_zero_of_global_log {γ γ' : ℝ → ℂ} {a b : ℝ}
    (hγ : ∃ L L' : ℝ → ℂ, (∀ t, HasDerivAt L (L' t) t) ∧ Continuous L' ∧ L b = L a ∧
      (∀ t, γ t = Complex.exp (L t)) ∧ (∀ t, γ' t = Complex.exp (L t) * L' t)) :
    logCurveIntegral γ γ' a b = 0 := by
  obtain ⟨L, L', hL, hL', hLab, hγL, hγ'L⟩ := hγ
  have h1 : γ = fun t => Complex.exp (L t) := funext hγL
  have h2 : γ' = fun t => Complex.exp (L t) * L' t := funext hγ'L
  rw [h1, h2, logCurveIntegral_of_global_log L L' hL hL' a b, hLab, sub_self]

/-- **Global obstruction.**  A loop with nonzero circulation admits no
single-valued `C¹` logarithm (hence no single-valued `C¹` phase) along it. -/
theorem no_global_log_of_winding_ne_zero {γ γ' : ℝ → ℂ} {a b : ℝ}
    (hwind : logCurveIntegral γ γ' a b ≠ 0) :
    ¬ ∃ L L' : ℝ → ℂ, (∀ t, HasDerivAt L (L' t) t) ∧ Continuous L' ∧ L b = L a ∧
      (∀ t, γ t = Complex.exp (L t)) ∧ (∀ t, γ' t = Complex.exp (L t) * L' t) :=
  fun h => hwind (logCurveIntegral_eq_zero_of_global_log h)

/-- The loop `t ↦ e^{int}`, `n ≠ 0`, on `[0, 2π]` has no single-valued `C¹`
logarithm: its phase is topologically locked to winding `n`. -/
theorem exp_int_loop_no_global_log (n : ℤ) (hn : n ≠ 0) :
    ¬ ∃ L L' : ℝ → ℂ, (∀ t, HasDerivAt L (L' t) t) ∧ Continuous L' ∧
      L (2 * Real.pi) = L 0 ∧
      (∀ t : ℝ, Complex.exp (Complex.I * n * t) = Complex.exp (L t)) ∧
      (∀ t : ℝ, Complex.exp (Complex.I * n * t) * (Complex.I * n) =
        Complex.exp (L t) * L' t) := by
  apply no_global_log_of_winding_ne_zero
  rw [logCurveIntegral_exp_int]
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hpi : ((Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hpi) Complex.I_ne_zero) hn'

/-- **Local polar identity.**  If `γ = ρ e^{iθ}` with `C¹` real amplitude
`ρ > 0` and phase `θ`, the phase circulation is `θ b - θ a`. -/
theorem polar_phaseCirculation (ρ ρ' θ θ' : ℝ → ℝ) (hρ : ∀ t, HasDerivAt ρ (ρ' t) t)
    (hθ : ∀ t, HasDerivAt θ (θ' t) t) (hρ' : Continuous ρ') (hθ' : Continuous θ')
    (hpos : ∀ t, 0 < ρ t) (a b : ℝ) :
    phaseCirculation (fun t => (ρ t : ℂ) * Complex.exp (Complex.I * θ t))
        (fun t => ((ρ' t : ℂ) + (ρ t : ℂ) * (Complex.I * θ' t)) * Complex.exp (Complex.I * θ t))
        a b = θ b - θ a := by
  -- `γ = exp (log ρ + i θ)`
  set L : ℝ → ℂ := fun t => ((Real.log (ρ t) : ℝ) : ℂ) + Complex.I * θ t with hL_def
  set L' : ℝ → ℂ := fun t => ((ρ' t / ρ t : ℝ) : ℂ) + Complex.I * θ' t with hL'_def
  have hLd : ∀ t, HasDerivAt L (L' t) t := by
    intro t
    have h1 := ((hρ t).log (hpos t).ne').ofReal_comp
    have h2 := (hθ t).ofReal_comp.const_mul Complex.I
    exact h1.add h2
  have hρc : Continuous ρ := continuous_iff_continuousAt.2 fun t => (hρ t).continuousAt
  have hL'c : Continuous L' := by
    have : Continuous fun t => ρ' t / ρ t := hρ'.div hρc fun t => (hpos t).ne'
    rw [hL'_def]; fun_prop
  have hγ : (fun t => (ρ t : ℂ) * Complex.exp (Complex.I * θ t)) = fun t => Complex.exp (L t) := by
    funext t
    rw [hL_def]
    simp only
    rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log (hpos t)]
  have hγ' : (fun t => ((ρ' t : ℂ) + (ρ t : ℂ) * (Complex.I * θ' t)) *
      Complex.exp (Complex.I * θ t)) = fun t => Complex.exp (L t) * L' t := by
    funext t
    rw [hL_def, hL'_def]
    simp only
    rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log (hpos t)]
    have hρne : (ρ t : ℂ) ≠ 0 := by exact_mod_cast (hpos t).ne'
    push_cast
    field_simp
  unfold phaseCirculation
  rw [hγ, hγ', logCurveIntegral_of_global_log L L' hLd hL'c a b]
  simp [hL_def]

/-! ### Additivity: E11 from the logarithmic derivative of products -/

/-- The logarithmic curve integral of a product is the sum. -/
theorem logCurveIntegral_mul {γ₁ γ₁' γ₂ γ₂' : ℝ → ℂ} (h₁ : C1NonvanishingCurve γ₁ γ₁')
    (h₂ : C1NonvanishingCurve γ₂ γ₂') (a b : ℝ) :
    logCurveIntegral (fun t => γ₁ t * γ₂ t) (fun t => γ₁' t * γ₂ t + γ₁ t * γ₂' t) a b =
      logCurveIntegral γ₁ γ₁' a b + logCurveIntegral γ₂ γ₂' a b := by
  unfold logCurveIntegral
  have hpt : ∀ t, (γ₁' t * γ₂ t + γ₁ t * γ₂' t) / (γ₁ t * γ₂ t) =
      γ₁' t / γ₁ t + γ₂' t / γ₂ t := by
    intro t
    have := h₁.ne t
    have := h₂.ne t
    field_simp
  simp_rw [hpt]
  exact intervalIntegral.integral_add (h₁.continuous_quotient.intervalIntegrable _ _)
    (h₂.continuous_quotient.intervalIntegrable _ _)

/-- The product of two `C¹` nonvanishing curves is `C¹` and nonvanishing. -/
theorem C1NonvanishingCurve.mul {γ₁ γ₁' γ₂ γ₂' : ℝ → ℂ} (h₁ : C1NonvanishingCurve γ₁ γ₁')
    (h₂ : C1NonvanishingCurve γ₂ γ₂') :
    C1NonvanishingCurve (fun t => γ₁ t * γ₂ t) (fun t => γ₁' t * γ₂ t + γ₁ t * γ₂' t) where
  hasDeriv := fun t => (h₁.hasDeriv t).mul (h₂.hasDeriv t)
  cont := (h₁.cont.mul h₂.continuous).add (h₁.continuous.mul h₂.cont)
  ne := fun t => mul_ne_zero (h₁.ne t) (h₂.ne t)

/-- **E11 additivity from geometry.**  If two closed loops have phase
circulations quantized by `n` and `m`, their product loop is quantized by
`n + m`. -/
theorem product_loop_windingQuantized {γ₁ γ₁' γ₂ γ₂' : ℝ → ℂ}
    (h₁ : C1NonvanishingCurve γ₁ γ₁') (h₂ : C1NonvanishingCurve γ₂ γ₂') {a b : ℝ} {n m : ℤ}
    (hn : WindingQuantized (phaseCirculation γ₁ γ₁' a b) n)
    (hm : WindingQuantized (phaseCirculation γ₂ γ₂' a b) m) :
    WindingQuantized
      (phaseCirculation (fun t => γ₁ t * γ₂ t) (fun t => γ₁' t * γ₂ t + γ₁ t * γ₂' t) a b)
      (n + m) := by
  have hsum : phaseCirculation (fun t => γ₁ t * γ₂ t)
      (fun t => γ₁' t * γ₂ t + γ₁ t * γ₂' t) a b =
        phaseCirculation γ₁ γ₁' a b + phaseCirculation γ₂ γ₂' a b := by
    unfold phaseCirculation
    rw [logCurveIntegral_mul h₁ h₂, Complex.add_im]
  rw [hsum]
  exact windingQuantized_add _ _ n m hn hm

/-! ### Fields on open subsets of real normed spaces -/

/-- **Curve-integral locking for fields.**  Let `ψ : E → ℂ` be `C¹` and
nonvanishing on an open set `U` of a real normed space and `c : ℝ → U` a
`C¹` loop.  Then `∮_c dψ/ψ = 2π i n` for an integer `n`. -/
theorem field_loop_winding_quantized {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ψ : E → ℂ) (ψ' : E → E →L[ℝ] ℂ) (U : Set E)
    (hψ : ∀ x ∈ U, HasFDerivAt ψ (ψ' x) x) (hψ'c : ContinuousOn ψ' U)
    (hne : ∀ x ∈ U, ψ x ≠ 0) (c c' : ℝ → E) (hc : ∀ t, HasDerivAt c (c' t) t)
    (hc' : Continuous c') (hcU : ∀ t, c t ∈ U) {a b : ℝ} (hclosed : c b = c a) :
    ∃ n : ℤ, logCurveIntegral (fun t => ψ (c t)) (fun t => ψ' (c t) (c' t)) a b =
      2 * Real.pi * Complex.I * n := by
  have hcc : Continuous c := continuous_iff_continuousAt.2 fun t => (hc t).continuousAt
  have hcurve : C1NonvanishingCurve (fun t => ψ (c t)) (fun t => ψ' (c t) (c' t)) :=
    ⟨fun t => (hψ (c t) (hcU t)).comp_hasDerivAt t (hc t),
      (hψ'c.comp_continuous hcc hcU).clm_apply hc', fun t => hne (c t) (hcU t)⟩
  exact winding_quantized hcurve (by simp only [hclosed])

/-! ### E4: the locking constant is fixed by the geometric winding -/

/-- **E4 from geometry.**  If along a loop the phase gradient satisfies the
pointwise lock `θ' = σ + α / w` (continuous `σ`, continuous nonvanishing `w`)
and the integrated phase gradient equals `2π n`, then
`α = alphaLock n (∫σ) (∫1/w)` whenever `∫1/w ≠ 0`. -/
theorem alpha_determined_by_winding (θ' σ w : ℝ → ℝ) (α : ℝ) (n : ℤ) {a b : ℝ}
    (hσ : Continuous σ) (hw : Continuous w) (hw0 : ∀ t, w t ≠ 0)
    (hlock : ∀ t, PointwiseLocked (θ' t) (σ t) (w t) α)
    (hwind : ∫ t in a..b, θ' t = 2 * Real.pi * n)
    (hden : ∫ t in a..b, (w t)⁻¹ ≠ 0) :
    α = alphaLock n (∫ t in a..b, σ t) (∫ t in a..b, (w t)⁻¹) := by
  have hinv : Continuous fun t => (w t)⁻¹ := hw.inv₀ hw0
  have hθ : (fun t => θ' t) = fun t => σ t + α * (w t)⁻¹ := by
    funext t; rw [hlock t, div_eq_mul_inv]
  have hint : ∫ t in a..b, θ' t = (∫ t in a..b, σ t) + α * ∫ t in a..b, (w t)⁻¹ := by
    rw [hθ, intervalIntegral.integral_add (hσ.intervalIntegrable _ _)
      ((continuous_const.mul hinv).intervalIntegrable _ _), intervalIntegral.integral_const_mul]
  unfold alphaLock
  rw [eq_div_iff hden, ← hwind, hint]
  ring

end

end WCTLean
