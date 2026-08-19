import Mathlib

namespace WCTLean

/-!
# Cross-equation derived constraints

These theorems do not promote the associated physical claims. They record
algebraic consequences that any calibrated WCT realization of those claims must
satisfy.
-/

/-- E19: frequency-gap quantity obtained from a curvature-squared spatial gap. -/
def gapCurvatureFrequency
    (c gapCoefficient sigma : ℝ) : ℝ :=
  c ^ 2 * (gapCoefficient * sigma ^ 2)

/-- E49/E19 bridge: the effective mass squared induced by the E19 frequency gap
is the curvature-mass square multiplied by the dimensionless gap coefficient. -/
noncomputable def effectiveMassSquaredFromGap
    (hbar c deltaOmega : ℝ) : ℝ :=
  hbar ^ 2 * deltaOmega / c ^ 4

/-- E19: combining `Delta_omega = c^2 C_gap sigma^2` with E49 gives
`m_eff^2 = C_gap (hbar sigma / c)^2`. -/
theorem gapCurvature_massSquared_chain
    (hbar c gapCoefficient sigma : ℝ)
    (hc : c ≠ 0) :
    effectiveMassSquaredFromGap hbar c
        (gapCurvatureFrequency c gapCoefficient sigma) =
      gapCoefficient * (hbar / c * sigma) ^ 2 := by
  unfold effectiveMassSquaredFromGap gapCurvatureFrequency
  field_simp [hc]

/-- E19/E6 consistency: unit gap coefficient reproduces the square of the
canonical curvature-mass law exactly. -/
theorem gapCurvature_unitCoefficient_recovers_massLawSquared
    (hbar c sigma : ℝ)
    (hc : c ≠ 0) :
    effectiveMassSquaredFromGap hbar c
        (gapCurvatureFrequency c 1 sigma) =
      (hbar / c * sigma) ^ 2 := by
  simpa using gapCurvature_massSquared_chain hbar c 1 sigma hc

/-- TOP7 diagnostic: curvature-energy density for a constant-curvature planar
sector. -/
def constantCurvatureEnergyDensity (kappa : ℝ) : ℝ :=
  kappa ^ 2

/-- TOP7 diagnostic: the torsion-free constant-curvature reduction of the E6
mass law. -/
noncomputable def planarConstantCurvatureMass
    (hbar c kappa : ℝ) : ℝ :=
  hbar / c * kappa

/-- TOP7 constraint: in the constant-curvature planar sector, the canonical
mass law is square-root in curvature energy: `m^2` is linear in `epsilon_kappa`.
This is not the same as a universal `m proportional to epsilon_kappa` law. -/
theorem planarConstantCurvatureMass_squared
    (hbar c kappa : ℝ) :
    planarConstantCurvatureMass hbar c kappa ^ 2 =
      (hbar / c) ^ 2 * constantCurvatureEnergyDensity kappa := by
  unfold planarConstantCurvatureMass constantCurvatureEnergyDensity
  ring

/-- Product of the first `steps` discrete retained fractions. Using an explicit
`Finset.prod` keeps the counting theorem independent of big-operator parser
notation. -/
noncomputable def retentionProduct
    (retention : ℕ → ℝ) (steps : ℕ) : ℝ :=
  (Finset.range steps).prod retention

@[simp] theorem retentionProduct_zero
    (retention : ℕ → ℝ) :
    retentionProduct retention 0 = 1 := by
  simp [retentionProduct]

@[simp] theorem retentionProduct_succ
    (retention : ℕ → ℝ) (steps : ℕ) :
    retentionProduct retention (Nat.succ steps) =
      retentionProduct retention steps * retention steps := by
  simp [retentionProduct, Finset.prod_range_succ]

/-- E41/E72: iterating genuine nonnegative count-retention bounds multiplies
the initial count by the product of the retained fractions. -/
theorem iterated_count_retention_bound
    (count retention : ℕ → ℝ) (steps : ℕ) :
    (∀ t < steps, 0 ≤ retention t) →
    (∀ t < steps, count (t + 1) ≤ retention t * count t) →
    count steps ≤ count 0 * retentionProduct retention steps := by
  induction steps with
  | zero =>
      intro _ _
      simp
  | succ steps ih =>
      intro hret hstep
      have hretPrev : ∀ t < steps, 0 ≤ retention t := by
        intro t ht
        exact hret t (Nat.lt_trans ht (Nat.lt_succ_self steps))
      have hstepPrev : ∀ t < steps, count (t + 1) ≤ retention t * count t := by
        intro t ht
        exact hstep t (Nat.lt_trans ht (Nat.lt_succ_self steps))
      have ihBound := ih hretPrev hstepPrev
      have hlast := hstep steps (Nat.lt_succ_self steps)
      have hretLast : 0 ≤ retention steps := hret steps (Nat.lt_succ_self steps)
      calc
        count (Nat.succ steps) ≤ retention steps * count steps := by
          simpa [Nat.succ_eq_add_one] using hlast
        _ ≤ retention steps * (count 0 * retentionProduct retention steps) :=
          mul_le_mul_of_nonneg_left ihBound hretLast
        _ = count 0 * retentionProduct retention (Nat.succ steps) := by
          rw [retentionProduct_succ]
          ring

/-- E28/E41/E72 exponent bookkeeping: once the logarithmic retention sum and
correction exponent use the same normalization, the `alpha*n` exponent splits
into the base count, correction, and retention contributions exactly. -/
noncomputable def alphaFromRetentionLogSum
    (n logRetentionSum beta : ℝ) : ℝ :=
  1 + logRetentionSum / n + beta

theorem alphaFromRetentionLogSum_exponent_identity
    (n logRetentionSum beta : ℝ) (hn : n ≠ 0) :
    n * alphaFromRetentionLogSum n logRetentionSum beta =
      n * (1 + beta) + logRetentionSum := by
  unfold alphaFromRetentionLogSum
  field_simp [hn]
  ring

/-- E22: raw derivative entry in the proposed complex-field metric correction. -/
noncomputable def complexMetricDerivativeEntry
    (a b : ℂ) : ℂ :=
  star a * b

/-- E22: the raw complex derivative correction is Hermitian under index swap. -/
theorem complexMetricDerivativeEntry_hermitian
    (a b : ℂ) :
    star (complexMetricDerivativeEntry a b) =
      complexMetricDerivativeEntry b a := by
  simp [complexMetricDerivativeEntry, mul_comm]

/-- E22: Hermitian is not the same as real symmetric.  The admissible derivative
pair `d₀ψ = 1`, `d₁ψ = i` gives opposite imaginary off-diagonal entries. -/
theorem complexMetricDerivativeEntry_not_symmetric_example :
    complexMetricDerivativeEntry (1 : ℂ) Complex.I ≠
      complexMetricDerivativeEntry Complex.I (1 : ℂ) := by
  intro h
  have him := congrArg Complex.im h
  norm_num [complexMetricDerivativeEntry] at him

/-- E22: taking the real part of the Hermitian derivative entry restores
symmetry under index exchange.  Nondegeneracy and Lorentzian signature remain
separate obligations. -/
theorem complexMetricDerivativeEntry_realPart_symmetric
    (a b : ℂ) :
    (complexMetricDerivativeEntry a b).re =
      (complexMetricDerivativeEntry b a).re := by
  calc
    (complexMetricDerivativeEntry a b).re =
        (star (complexMetricDerivativeEntry a b)).re := by simp
    _ = (complexMetricDerivativeEntry b a).re := by
      rw [complexMetricDerivativeEntry_hermitian]

end WCTLean