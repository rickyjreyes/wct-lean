import Mathlib

/-! Frozen two-dimensional D4: exact algebra and conditional whole-space analysis.
The chosen H² carrier and weak Laplacian are explicit inputs, not instantiated
Sobolev infrastructure. No periodic numerical candidate is identified here. -/

namespace WCTLean.D4

noncomputable section

open Filter Topology MeasureTheory

abbrev Plane := Fin 2 → ℝ
abbrev Field := Plane → ℂ

structure WholeSpaceData where
  H2 : Set Field
  weakLaplacian : Field → Field

abbrev State (data : WholeSpaceData) := {u : Field // u ∈ data.H2}

noncomputable def mass (data : WholeSpaceData) (u : State data) : ℝ :=
  ∫ x : Plane, ‖u.val x‖^2

noncomputable def hamiltonian (data : WholeSpaceData) (k β γ : ℝ) (u : State data) : ℝ :=
  (∫ x : Plane, ‖data.weakLaplacian u.val x + (k : ℂ)^2*u.val x‖^2)
    - β/2*(∫ x : Plane, ‖u.val x‖^4) + γ/3*(∫ x : Plane, ‖u.val x‖^6)

noncomputable def I2 (data : WholeSpaceData) (k β γ m : ℝ) : ℝ :=
  sInf {e : ℝ | ∃ u : State data, mass data u = m ∧ hamiltonian data k β γ u = e}

def minimizers (data : WholeSpaceData) (k β γ m : ℝ) : Set (State data) :=
  {u | mass data u = m ∧ hamiltonian data k β γ u = I2 data k β γ m}

def frozenBeta : ℝ := 4608178181141995 / 1125899906842624
def frozenMass : ℝ := 1432536998431173 / 562949953421312
def frozenRho : ℝ := 1 + 3*frozenBeta/32
noncomputable def frozenThreshold : ℝ := 3/Real.sqrt frozenRho

theorem frozen_beta_pos : 0 < frozenBeta := by norm_num [frozenBeta]
theorem frozen_mass_pos : 0 < frozenMass := by norm_num [frozenMass]
theorem frozen_rho_pos : 0 < frozenRho := by norm_num [frozenRho, frozenBeta]

theorem frozen_rho_exact : frozenRho = 49853331562389953 / 36028797018963968 := by
  norm_num [frozenRho, frozenBeta]

theorem frozen_margin_exact : 9-frozenRho*frozenMass^2 =
    454708712324087584212476662678391978900775591 /
    11417981541647679048466287755595961091061972992 := by
  norm_num [frozenRho, frozenBeta, frozenMass]

theorem frozen_margin_pos : 0 < 9-frozenRho*frozenMass^2 := by
  rw [frozen_margin_exact]
  norm_num

theorem frozen_threshold_pos : 0 < frozenThreshold := by
  exact div_pos (by norm_num) (Real.sqrt_pos.2 frozen_rho_pos)

/-- Fully instantiated threshold: exact dyadics and a proved square-root step. -/
theorem frozen_below_threshold : frozenMass < frozenThreshold := by
  have hs := Real.sqrt_pos.2 frozen_rho_pos
  have hsq := Real.sq_sqrt frozen_rho_pos.le
  have hp : (frozenMass*Real.sqrt frozenRho)^2 = frozenMass^2*frozenRho := by
    rw [mul_pow, hsq]
  have hx : frozenMass*Real.sqrt frozenRho < 3 := by
    nlinarith [frozen_margin_pos, sq_nonneg (frozenMass*Real.sqrt frozenRho-3)]
  exact (lt_div_iff₀ hs).2 hx

theorem nonlinear_square_completion (β γ r : ℝ) (hγ : γ ≠ 0) :
    -β/2*r^2+γ/3*r^3 = γ/3*r*(r-3*β/(4*γ))^2-3*β^2/(16*γ)*r := by
  field_simp [hγ]
  ring

def dilationEnergy (P B C lam : ℝ) : ℝ := P*lam^4-B*lam^2+C

theorem dilation_polynomial (D K Q S M k β γ lam : ℝ) :
    lam^4*D-2*k^2*lam^2*K+k^4*M-β/2*lam^2*Q+γ/3*lam^4*S =
    dilationEnergy (D+γ*S/3) (2*k^2*K+β*Q/2) (k^4*M) lam := by
  unfold dilationEnergy
  ring

theorem dilation_gap (P B C lam : ℝ) (hP : P ≠ 0) :
    dilationEnergy P B C lam-(C-B^2/(4*P)) = P*(lam^2-B/(2*P))^2 := by
  unfold dilationEnergy
  field_simp [hP]
  ring

theorem dilation_lower_bound (P B C lam : ℝ) (hP : 0 < P) :
    C-B^2/(4*P) ≤ dilationEnergy P B C lam := by
  have h := mul_nonneg hP.le (sq_nonneg (lam^2-B/(2*P)))
  rw [← dilation_gap P B C lam hP.ne'] at h
  linarith

theorem dilation_unique_positive (P B C lam : ℝ) (hP : 0 < P) (hB : 0 < B)
    (hlam : 0 < lam) :
    dilationEnergy P B C lam = C-B^2/(4*P) ↔ lam = Real.sqrt (B/(2*P)) := by
  have hz : 0 < B/(2*P) := div_pos hB (by positivity)
  have hs := Real.sq_sqrt hz.le
  have hsp := Real.sqrt_pos.2 hz
  constructor
  · intro he
    have hg := dilation_gap P B C lam hP.ne'
    rw [he, sub_self] at hg
    have hzero : (lam^2-B/(2*P))^2 = 0 := (mul_eq_zero.mp hg.symm).resolve_left hP.ne'
    have heq := sq_eq_zero_iff.mp hzero
    nlinarith
  · intro he
    subst lam
    have hg := dilation_gap P B C (Real.sqrt (B/(2*P))) hP.ne'
    rw [hs] at hg
    nlinarith

theorem dilation_virial (P B lam : ℝ) (hP : P ≠ 0) (h : lam^2 = B/(2*P)) :
    P*lam^4-B*lam^2/2 = 0 := by
  have hm := (eq_div_iff (mul_ne_zero (by norm_num : (2:ℝ) ≠ 0) hP)).1 h
  nlinarith [congrArg (fun x : ℝ => x*lam^2) hm]

theorem improved_square_identity (D T K Q S M k β γ : ℝ) (hγ : γ ≠ 0)
    (hT : T = D-2*k^2*K+k^4*M) (hV : D-k^2*K-β*Q/4+γ*S/3 = 0) :
    D+T+(2*γ/3)*(S-3*β/(4*γ)*Q+9*β^2/(64*γ^2)*M) = (k^4+3*β^2/(32*γ))*M := by
  have identity : D+T+(2*γ/3)*(S-3*β/(4*γ)*Q+9*β^2/(64*γ^2)*M)
      -(k^4+3*β^2/(32*γ))*M = 2*(D-k^2*K-β*Q/4+γ*S/3) := by
    rw [hT]
    field_simp [hγ]
    ring
  rw [hV] at identity
  linarith

theorem improved_D_bound (D T W ρ M γ : ℝ) (hT : 0 ≤ T) (hW : 0 ≤ W)
    (hγ : 0 ≤ γ) (hid : D+T+(2*γ/3)*W = ρ*M) : D ≤ ρ*M := by
  nlinarith [mul_nonneg hγ hW]

/-- The analytic Fourier estimate is an input; this discharges its scalar use. -/
theorem sobolev_cap_from_D_bound (U D ρ M : ℝ) (hρ : 0 ≤ ρ) (hM : 0 ≤ M)
    (hD : D ≤ ρ*M) (hU : U ≤ Real.sqrt (M*D)/4) :
    U ≤ Real.sqrt ρ*M/4 := by
  have hp : M*D ≤ (Real.sqrt ρ*M)^2 := by
    rw [mul_pow, Real.sq_sqrt hρ]
    nlinarith [mul_le_mul_of_nonneg_left hD hM]
  have hs := Real.sqrt_le_sqrt hp
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg ρ) hM)] at hs
  linarith

theorem L6_L4_ratio_from_cap (S Q U L M : ℝ) (hQ : 0 ≤ Q)
    (hS : S ≤ U*Q) (hU : U ≤ L*M) : S ≤ L*M*Q :=
  hS.trans (mul_le_mul_of_nonneg_right hU hQ)

/-- Convert the source L6/L4 estimate into the precise amplitude coefficient. -/
theorem amplitude_ratio_from_L6_bound (β γ L B a b Q S : ℝ)
    (hγ : 0 ≤ γ) (hB : 0 < B) (ha : 0 < a) (hb : 0 ≤ b)
    (hbalance : γ*L*B = 3*β/4) (hS : S ≤ L*a*Q) :
    γ*(b/a+1)*S/3 ≤ β*((a+b)/(2*B))*Q/2 := by
  have hc : 0 ≤ γ*(b/a+1)/3 := by positivity
  have h := mul_le_mul_of_nonneg_left hS hc
  have heq : γ*(b/a+1)/3*(L*a*Q) = β*((a+b)/(2*B))*Q/2 := by
    calc
      _ = (γ*L*B)*((a+b)*Q)/(3*B) := by field_simp; ring
      _ = _ := by rw [hbalance]; ring
  rw [heq] at h
  nlinarith

def profileEnergy (β γ T Q S : ℝ) : ℝ := T-β*Q/2+γ*S/3
def amplitudePerMass (β γ T Q S t : ℝ) : ℝ := T-β*t*Q/2+γ*t^2*S/3

theorem amplitude_bound (β γ T Q S t h : ℝ) (ht : 1 ≤ t) (hh : 0 ≤ h)
    (hT : 0 ≤ T) (hS : 0 ≤ γ*S) (hr : γ*(t+1)*S/3 ≤ β*(1-h)*Q/2) :
    amplitudePerMass β γ T Q S t ≤ (1+(t-1)*h)*profileEnergy β γ T Q S := by
  have hE : -β*Q/2 ≤ profileEnergy β γ T Q S := by unfold profileEnergy; linarith
  have ha := mul_le_mul_of_nonneg_left hr (sub_nonneg.2 ht)
  have hb := mul_le_mul_of_nonneg_left hE (mul_nonneg (sub_nonneg.2 ht) hh)
  unfold amplitudePerMass profileEnergy at *
  nlinarith

/-- These analytic premises remain to be instantiated for the defined H² infimum.
They assert sequences and amplitude trials, not strict binding or attainment. -/
structure BindingSequenceInputs (I : ℝ → ℝ) (β γ B : ℝ) : Prop where
  negative : ∀ a, 0 < a → I a < 0
  adjusted : ∀ a b, 0 < a → a < b → a+b < 2*B →
    ∃ T Q S : ℕ → ℝ,
      Tendsto (fun n => profileEnergy β γ (T n) (Q n) (S n)) atTop (𝓝 (I a)) ∧
      ∀ n, 0 ≤ T n ∧ 0 ≤ γ*S n ∧
        γ*(b/a+1)*S n/3 ≤ β*((a+b)/(2*B))*Q n/2 ∧
        I b/(b/a) ≤ amplitudePerMass β γ (T n) (Q n) (S n) (b/a)

theorem infimum_scaling_bound (I : ℝ → ℝ) (β γ B a b : ℝ)
    (inputs : BindingSequenceInputs I β γ B) (hB : 0 < B)
    (ha : 0 < a) (hab : a < b) (hspan : a+b < 2*B) :
    I b/(b/a) ≤ (1+(b/a-1)*(1-(a+b)/(2*B)))*I a := by
  obtain ⟨T,Q,S,hlim,hrows⟩ := inputs.adjusted a b ha hab hspan
  have ht : 1 ≤ b/a := (one_le_div ha).2 hab.le
  have hh : 0 ≤ 1-(a+b)/(2*B) := by
    have := (div_lt_one (by positivity : 0 < 2*B)).2 hspan
    linarith
  have hbound : ∀ n, I b/(b/a) ≤ (1+(b/a-1)*(1-(a+b)/(2*B)))*profileEnergy β γ (T n) (Q n) (S n) := by
    intro n
    obtain ⟨hT,hS,hr,hi⟩ := hrows n
    apply hi.trans (amplitude_bound β γ (T n) (Q n) (S n) (b/a) (1-(a+b)/(2*B)) ht hh hT hS ?_)
    convert hr using 1; ring
  have hlimit : Tendsto (fun n : ℕ => (1+(b/a-1)*(1-(a+b)/(2*B)))*profileEnergy β γ (T n) (Q n) (S n))
      atTop (𝓝 ((1+(b/a-1)*(1-(a+b)/(2*B)))*I a)) := tendsto_const_nhds.mul hlim
  exact ge_of_tendsto hlimit (Eventually.of_forall hbound)

theorem quantitative_gap (I : ℝ → ℝ) (B a b : ℝ) (hB : 0 < B)
    (ha : 0 < a) (hab : a < b) (hspan : a+b < 2*B) (hI : I a < 0)
    (hscale : I b/(b/a) ≤ (1+(b/a-1)*(1-(a+b)/(2*B)))*I a) :
    (b-a)*(-I a)/a^2*(1-(a+b)/(2*B)) ≤ I a/a-I b/b ∧
    0 < (b-a)*(-I a)/a^2*(1-(a+b)/(2*B)) := by
  have hb : 0 < b := lt_trans ha hab
  have hh : 0 < 1-(a+b)/(2*B) := by
    have := (div_lt_one (by positivity : 0 < 2*B)).2 hspan
    linarith
  have hn := div_nonneg (sub_nonneg.2 hscale) ha.le
  have heq : I a/a-I b/b-(b-a)*(-I a)/a^2*(1-(a+b)/(2*B)) =
      ((1+(b/a-1)*(1-(a+b)/(2*B)))*I a-I b/(b/a))/a := by
    field_simp [ha.ne', hb.ne', hB.ne']
    ring
  constructor
  · rw [← heq] at hn
    linarith
  · exact mul_pos (div_pos (mul_pos (sub_pos.2 hab) (neg_pos.2 hI)) (sq_pos_of_pos ha)) hh

theorem binding_of_strict_energy_per_mass (I : ℝ → ℝ) (m μ : ℝ)
    (hm : 0 < m) (hμ : 0 < μ) (hμm : μ < m)
    (hmono : ∀ a, 0 < a → a < m → I m/m < I a/a) : I m < I μ+I (m-μ) := by
  have hb : 0 < m-μ := sub_pos.2 hμm
  have h1 := mul_lt_mul_of_pos_left (hmono μ hμ hμm) hμ
  have h2 := mul_lt_mul_of_pos_left (hmono (m-μ) hb (by linarith)) hb
  have hμcancel : μ*(I μ/μ) = I μ := by field_simp [hμ.ne']
  have hbcancel : (m-μ)*(I (m-μ)/(m-μ)) = I (m-μ) := by field_simp [hb.ne']
  have hmcancel : m*(I m/m) = I m := by field_simp [hm.ne']
  rw [hμcancel] at h1
  rw [hbcancel] at h2
  nlinarith

/-- Conditional frozen binding; the exact mass threshold is discharged above. -/
theorem frozen_strict_binding (I : ℝ → ℝ)
    (inputs : BindingSequenceInputs I frozenBeta frozenBeta frozenThreshold)
    (μ : ℝ) (hμ : 0 < μ) (hμm : μ < frozenMass) : I frozenMass < I μ+I (frozenMass-μ) := by
  apply binding_of_strict_energy_per_mass I frozenMass μ frozen_mass_pos hμ hμm
  intro a ha ham
  have span : a+frozenMass < 2*frozenThreshold := by linarith [frozen_below_threshold]
  have scale := infimum_scaling_bound I frozenBeta frozenBeta frozenThreshold a frozenMass inputs frozen_threshold_pos ha ham span
  have gap := quantitative_gap I frozenThreshold a frozenMass frozen_threshold_pos ha ham span (inputs.negative a ha) scale
  linarith [gap.1, gap.2]

/-- Conditional specialization to the declared whole-space infimum. -/
theorem frozen_I2_strict_binding (data : WholeSpaceData)
    (inputs : BindingSequenceInputs (I2 data 1 frozenBeta frozenBeta)
      frozenBeta frozenBeta frozenThreshold)
    (μ : ℝ) (hμ : 0 < μ) (hμm : μ < frozenMass) :
    I2 data 1 frozenBeta frozenBeta frozenMass <
      I2 data 1 frozenBeta frozenBeta μ + I2 data 1 frozenBeta frozenBeta (frozenMass-μ) :=
  frozen_strict_binding _ inputs μ hμ hμm

/-- Sequential compactness modulo translations is an explicit analytic input.
No minimizer or attained infimum is assumed. -/
structure VariationalCompactnessInputs (X : Type*) [TopologicalSpace X]
    (M H : X → ℝ) (I : ℝ → ℝ) (translate : Plane → X → X) (m : ℝ) : Prop where
  mass_continuous : Continuous M
  energy_continuous : Continuous H
  translation_mass : ∀ y u, M (translate y u) = M u
  translation_energy : ∀ y u, H (translate y u) = H u
  minimizing_sequence : ∃ u : ℕ → X,
    (∀ n, M (u n) = m) ∧ Tendsto (fun n => H (u n)) atTop (𝓝 (I m))
  compactness : ∀ u : ℕ → X,
    (∀ n, M (u n) = m) → Tendsto (fun n => H (u n)) atTop (𝓝 (I m)) →
    ∃ (φ : ℕ → ℕ) (y : ℕ → Plane) (v : X),
      StrictMono φ ∧ Tendsto (fun n => translate (y n) (u (φ n))) atTop (𝓝 v)

theorem attainment_of_compactness (X : Type*) [TopologicalSpace X]
    (M H : X → ℝ) (I : ℝ → ℝ) (translate : Plane → X → X)
    (m : ℝ) (inputs : VariationalCompactnessInputs X M H I translate m) :
    ∃ v : X, M v = m ∧ H v = I m := by
  obtain ⟨u, hM, hH⟩ := inputs.minimizing_sequence
  obtain ⟨φ, y, v, hφ, hv⟩ := inputs.compactness u hM hH
  have hmseq : Tendsto (fun n => M (translate (y n) (u (φ n)))) atTop (𝓝 m) := by
    simpa only [inputs.translation_mass, hM] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => m) atTop (𝓝 m))
  have heseq : Tendsto (fun n => H (translate (y n) (u (φ n)))) atTop (𝓝 (I m)) := by
    simpa only [inputs.translation_energy, Function.comp_def] using hH.comp hφ.tendsto_atTop
  exact ⟨v, tendsto_nhds_unique ((inputs.mass_continuous.tendsto v).comp hv) hmseq,
    tendsto_nhds_unique ((inputs.energy_continuous.tendsto v).comp hv) heseq⟩

theorem frozen_minimizers_nonempty (data : WholeSpaceData)
    [TopologicalSpace (State data)] (translate : Plane → State data → State data)
    (inputs : VariationalCompactnessInputs (State data) (mass data)
      (hamiltonian data 1 frozenBeta frozenBeta) (I2 data 1 frozenBeta frozenBeta) translate frozenMass) :
    (minimizers data 1 frozenBeta frozenBeta frozenMass).Nonempty :=
  attainment_of_compactness _ _ _ _ translate frozenMass inputs

/-- Conservation and energy trapping imply all-time control. The H² distance
to the full minimizing set and the analytic hypotheses remain to be instantiated. -/
theorem stability_from_energy_trapping (X : Type*) (M H d : X → ℝ)
    (flow : ℝ → X → X) (m Emin : ℝ)
    (mass_conserved : ∀ t u, M (flow t u) = M u)
    (energy_conserved : ∀ t u, H (flow t u) = H u)
    (initial_energy_control : ∀ η > 0, ∃ δ > 0, ∀ u,
      M u = m → d u < δ → H u < Emin+η)
    (trapping : ∀ ε > 0, ∃ η > 0, ∀ u,
      M u = m → H u < Emin+η → d u < ε) :
    ∀ ε > 0, ∃ δ > 0, ∀ u, M u = m → d u < δ → ∀ t, d (flow t u) < ε := by
  intro ε hε
  obtain ⟨η, hη, htrap⟩ := trapping ε hε
  obtain ⟨δ, hδ, hinit⟩ := initial_energy_control η hη
  refine ⟨δ, hδ, ?_⟩
  intro u hmass hdist t
  apply htrap (flow t u)
  · rw [mass_conserved, hmass]
  · rw [energy_conserved]
    exact hinit u hmass hdist

end

end WCTLean.D4

