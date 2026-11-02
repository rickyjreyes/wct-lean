import Mathlib
import WCTLean.Models.ComplexCurvature

namespace WCTLean

/-!
# Registry-only mathematical closures: TOP6, CM3/CM4, CM10, CM15/CM20,
# E44, E60, E82

Every result below is an explicitly scoped mathematical statement.
None derives the WCT cosmological field equations, identifies a physical
eigenmode, proves a knot classification, or establishes empirical validity.
-/

/-! ## TOP6: curvature-band scaling obstruction -/

/-- The dimensionful registry statistic epsilon_kappa = (int kappa^2 ds)/L.
The integral and length are supplied as real scalar data. -/
noncomputable def top6CurvatureStatistic (length totalSquaredCurvature : ℝ) : ℝ :=
  totalSquaredCurvature / length

/-- Under a positive geometric dilation a, the length scales by a and
the curvature-squared integral by 1/a. The statistic scales as 1/a^2.
The geometric scaling laws themselves are explicit inputs to this scalar theorem. -/
theorem top6_statistic_scales_inverse_square
    (length totalSquaredCurvature a : ℝ)
    (hL : length ≠ 0) (ha : a ≠ 0) :
    top6CurvatureStatistic (a * length) (totalSquaredCurvature / a) =
      top6CurvatureStatistic length totalSquaredCurvature / a ^ 2 := by
  unfold top6CurvatureStatistic
  field_simp [hL, ha]
  <;> ring

/-- A dilation by two gives a distinct numerical statistic whenever the
original curvature-squared integral is positive. -/
theorem top6_dilation_changes_statistic
    (length totalSquaredCurvature : ℝ)
    (hL : 0 < length) (hcurv : 0 < totalSquaredCurvature) :
    top6CurvatureStatistic (2 * length) (totalSquaredCurvature / 2) <
      top6CurvatureStatistic length totalSquaredCurvature := by
  have hL0 : length ≠ 0 := ne_of_gt hL
  rw [top6_statistic_scales_inverse_square length totalSquaredCurvature 2 hL0
    (by norm_num)]
  have hpos : 0 < top6CurvatureStatistic length totalSquaredCurvature :=
    div_pos hcurv hL
  norm_num
  linarith

/-! ## CM3 and CM4: the potential/decay compatibility check -/

/-- The CM3 Fourier-space Poisson-like algebra holds at nonzero wave number. -/
theorem cm3_potential_poisson_relation
    (theta coefficient wavenumber : ℝ) (hk : wavenumber ≠ 0) :
    wavenumber ^ 2 * (-coefficient * theta / wavenumber ^ 2) =
      -coefficient * theta := by
  field_simp [hk]
  <;> ring

/-- For a nonzero constant coupling a and nonzero mode theta, if
thetaDot = rate * theta, then phiDot = -|rate| phi is equivalent to
rate <= 0. This is the exact compatibility test of CM3 with CM4.
It does not assume that the supplied mode obeys a WCT field equation. -/
theorem cm4_decay_iff_nonpositive_logarithmic_rate
    (a theta rate : ℝ) (ha : a ≠ 0) (hTheta : theta ≠ 0) :
    (a * (rate * theta) = -|rate| * (a * theta)) ↔ rate ≤ 0 := by
  have hat : a * theta ≠ 0 := mul_ne_zero ha hTheta
  constructor
  · intro h
    have heq : (a * theta) * rate = (a * theta) * (-|rate|) := by
      calc
        (a * theta) * rate = a * (rate * theta) := by ring
        _ = -|rate| * (a * theta) := h
        _ = (a * theta) * (-|rate|) := by ring
    have hr : rate = -|rate| := mul_left_cancel₀ hat heq
    rw [hr]
    exact neg_nonpos.mpr (abs_nonneg rate)
  · intro hr
    rw [abs_of_nonpos hr]
    ring

/-! ## CM10: finite drag is a contraction -/

/-- Convex tight-coupling drag shrinks the absolute baryon/photon mismatch.
No dynamical coupling law beyond the displayed discrete update is claimed. -/
theorem cm10_drag_contracts_difference
    (baryon photon drag : ℝ)
    (hdrag0 : 0 ≤ drag) (hdrag1 : drag ≤ 1) :
    |(1 - drag) * baryon + drag * photon - photon| ≤
      |baryon - photon| := by
  have hweight0 : 0 ≤ 1 - drag := by linarith
  have hweight1 : 1 - drag ≤ 1 := by linarith
  have hfactor :
      (1 - drag) * baryon + drag * photon - photon =
        (1 - drag) * (baryon - photon) := by ring
  rw [hfactor, abs_mul, abs_of_nonneg hweight0]
  have hbound := mul_le_mul_of_nonneg_right hweight1
    (abs_nonneg (baryon - photon))
  simpa using hbound

/-! ## CM15 + CM20: expansion/energy compatibility -/

/-- The Hubble-like logarithmic derivative implied by the CM15 definition
a(t) = (E(0)/E(t))^(1/3), once the energy is differentiable and positive. -/
noncomputable def cm15ImpliedHubble (energy energyDot : ℝ) : ℝ :=
  -energyDot / (3 * energy)

/-- The nonnegative branch of the proposed CM20 expansion ansatz. -/
noncomputable def cm20ProposedHubble (thetaDensity K : ℝ) : ℝ :=
  Real.sqrt (thetaDensity / (3 * |K|))

/-- CM15 and CM20 agree precisely when the curvature energy obeys this
specific loss-rate identity. This is an algebraic necessary-and-sufficient
condition, not a proof of a physical Friedmann equation. -/
theorem cm15_cm20_compatible_iff_energy_loss
    (energy energyDot thetaDensity K : ℝ) (henergy : energy ≠ 0) :
    cm15ImpliedHubble energy energyDot =
        cm20ProposedHubble thetaDensity K ↔
      energyDot = -3 * energy * cm20ProposedHubble thetaDensity K := by
  unfold cm15ImpliedHubble
  have hden : 3 * energy ≠ 0 := mul_ne_zero (by norm_num) henergy
  constructor
  · intro h
    have hp := (div_eq_iff hden).mp h
    calc
      energyDot = -(-energyDot) := by ring
      _ = -3 * energy * cm20ProposedHubble thetaDensity K := by rw [hp]; ring
  · intro h
    rw [h]
    field_simp [henergy]
    <;> ring

/-! ## E44: global phase covariance obstruction of the theta eigenproblem -/

/-- A local expression with a phase-invariant denominator and the corrected
conjugate numerator is unchanged by a constant unit complex rotation. -/
theorem e44_local_curvature_global_phase_invariance
    (phase lapPsi psi denominator : ℂ)
    (hunit : phase * star phase = 1) :
    -(phase * lapPsi) * (star (phase * psi) / denominator) =
      -lapPsi * (star psi / denominator) := by
  rw [star_mul]
  calc
    -(phase * lapPsi) * (star psi * star phase / denominator) =
        (phase * star phase) * (-lapPsi * (star psi / denominator)) := by ring
    _ = -lapPsi * (star psi / denominator) := by rw [hunit]; ring

/-- If theta is invariant under rotation, both the original and rotated
nonlinear eigenvalue equations with the SAME lambda imply lambda*psi=0,
unless the phase rotation is trivial. This is a conditional obstruction to
treating thetaComplex as a complex-linear eigenoperator. -/
theorem e44_phase_rotated_eigenvalue_obstruction
    (phase psi eigenvalue theta : ℂ) (hphase : phase ≠ 1)
    (hbase : theta = eigenvalue * psi)
    (hrotated : theta = eigenvalue * (phase * psi)) :
    eigenvalue * psi = 0 := by
  have heq : eigenvalue * psi = eigenvalue * (phase * psi) :=
    hbase.symm.trans hrotated
  have hz : (1 - phase) * (eigenvalue * psi) = 0 := by
    calc
      (1 - phase) * (eigenvalue * psi) =
          eigenvalue * psi - eigenvalue * (phase * psi) := by ring
      _ = 0 := sub_eq_zero.mpr heq
  exact (mul_eq_zero.mp hz).resolve_left
    (sub_ne_zero.mpr (Ne.symm hphase))

/-! ## E60: exact real-amplitude reduction -/

/-- Squared-amplitude evolution under the declared real cubic amplitude ODE. -/
theorem e60_real_squared_amplitude_derivative
    (amplitude : ℝ → ℝ) (t mu g : ℝ)
    (hODE : HasDerivAt amplitude
      (mu * amplitude t - g * (amplitude t) ^ 3) t) :
    HasDerivAt (fun s => (amplitude s) ^ 2)
      (2 * mu * (amplitude t) ^ 2 - 2 * g * (amplitude t) ^ 4) t := by
  convert hODE.pow 2 using 1 <;> ring

/-- Complete algebraic stationary-state classification for the real scalar
amplitude ODE: a = 0 or mu = g*a^2. -/
theorem e60_real_stationary_iff
    (amplitude mu g : ℝ) :
    mu * amplitude - g * amplitude ^ 3 = 0 ↔
      amplitude = 0 ∨ mu = g * amplitude ^ 2 := by
  have hfactor :
      mu * amplitude - g * amplitude ^ 3 =
        amplitude * (mu - g * amplitude ^ 2) := by ring
  rw [hfactor, mul_eq_zero, sub_eq_zero]

/-! ## E82: finite Gram tensor and positive-semidefinite quadratic form -/

/-- Finite Gram tensor of feature derivatives. The inner-product convention
is real and the feature count is finite. -/
noncomputable def e82InformationGram
    {n m : ℕ} (features : Fin n → Fin m → ℝ) (i j : Fin n) : ℝ :=
  ∑ k, features i k * features j k

theorem e82_information_gram_symmetric
    {n m : ℕ} (features : Fin n → Fin m → ℝ) (i j : Fin n) :
    e82InformationGram features i j = e82InformationGram features j i := by
  unfold e82InformationGram
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem e82_information_gram_diagonal_nonnegative
    {n m : ℕ} (features : Fin n → Fin m → ℝ) (i : Fin n) :
    0 ≤ e82InformationGram features i i := by
  unfold e82InformationGram
  apply Finset.sum_nonneg
  intro k _
  nlinarith [sq_nonneg (features i k)]

/-- Gram quadratic form written as a sum of squares. -/
noncomputable def e82InformationGramQuadratic
    {n m : ℕ} (features : Fin n → Fin m → ℝ) (v : Fin n → ℝ) : ℝ :=
  ∑ k, (∑ i, v i * features i k) ^ 2

/-- The quadratic form of the finite Gram tensor is nonnegative.
The link to the indexed matrix expression is the distributive identity
sum_ij v_i g_ij v_j = sum_k (sum_i v_i features_ik)^2. -/
theorem e82_information_gram_quadratic_nonnegative
    {n m : ℕ} (features : Fin n → Fin m → ℝ) (v : Fin n → ℝ) :
    0 ≤ e82InformationGramQuadratic features v := by
  unfold e82InformationGramQuadratic
  exact Finset.sum_nonneg (fun k _ => sq_nonneg _)

end WCTLean
