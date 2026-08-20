# WCT Lean Formal Coverage Index

This index separates **canonical registration**, **equation-specific typed support**, **kernel-proved content**, and **physical validation**.

## Canonical navigation

- [Corrected 142-object equation registry](https://github.com/rickyjreyes/geometry_of_resonance/blob/main/WCT_FULL_EQUATION_LIST_CORRECTED.md)
- [Master equation architecture](https://github.com/rickyjreyes/geometry_of_resonance/blob/main/WCT_MASTER_EQUATIONS_UPDATED.md)
- [Complete SymPy classification](https://github.com/rickyjreyes/wct-sympy/blob/main/VERIFICATION_INDEX.md)
- [Lean theorem inventory](THEOREMS.md)
- [SymPy-to-Lean map](SYMPY_MAP.md)
- [Public research-corpus map](https://rickyjreyes.github.io/research-corpus/)

The canonical registry defines equation text, symbols, assumptions, and scientific boundaries. Lean claims only what its declarations encode and what the kernel accepts under displayed hypotheses.

## Layer 1 — Compiled canonical registration: 142 / 142

`WCTLean/Registry.lean` compiles every canonical ID:

| Family | Count |
|---|---:|
| Master systems | 9 |
| Canonical equations | 83 |
| Curvature-locked electron equations | 10 |
| Auxiliary equations | 5 |
| Cosmology equations | 20 |
| Topology equations | 9 |
| Correction equations | 6 |
| **Total** | **142** |

Lean proves registry length, family partition, status partition, uniqueness, and completeness through:

```lean
masterIds_length
canonicalIds_length
electronIds_length
auxiliaryIds_length
cosmologyIds_length
topologyIds_length
correctionIds_length
allEquationIds_length
allEquationIds_nodup
statusPartition_length
statusPartition_nodup
statusPartition_complete
every_registered_id_has_status
every_registered_id_has_family
canonicalRegistry_length
```

The effective symbolic-audit partition inherited from the current `wct-sympy` main branch is:

| Status | Count |
|---|---:|
| `PASS` | 68 |
| `CONDITIONAL` | 18 |
| `DEFINITION` | 26 |
| `OPEN` | 30 |
| **Total** | **142** |

These are inherited symbolic-audit classifications, not Lean theorem counts. The active SymPy expansion PR is intentionally tracked separately until it is merged to `wct-sympy` main.

## Layer 2 — Non-registry typed Lean support: 80 IDs

The following IDs have a maintained equation-specific definition, proposition, theorem, counterexample, analytic contract, or kernel-checked constraint beyond registry metadata:

```text
M1 M2 M3 M4 M5 M6A M6B M7
E1A E1B E2 E3 E4 E5 E6 E7 E8 E9 E10 E11
E12 E13 E14 E16 E17 E18 E19 E20 E22
E24 E25 E26 E27 E28 E29 E32 E33 E36 E37 E38 E41
E45 E47 E49 E50 E51 E53
E57 E58 E59 E61 E62 E64
E65 E66 E67 E68 E69 E70 E72
E78 E81
CLE4 CLE5 CLE8 CLE9 CLE10
G1 EX EY EZ FA
CM9 CM11 CM12 CM13 CM16
TOP3 TOP7
CORR2
```

The branch's kernel-checked coverage expansion adds eighteen IDs relative to the original 62-ID baseline:

```text
E16 E19 E22 E32 E37 E38 E41 E50 E72
CLE4 CLE5 CLE8 CLE9 CLE10
CM11 TOP3 TOP7 CORR2
```

Some of these are exact conditional constraints rather than proofs of the full physical claim. They count as equation-specific formal support because the theorem itself is kernel-checked; they do **not** change the scientific status of the associated canonical claim unless a separate symbolic or analytic audit justifies that change.

### Direct algebraic, order-theoretic, counting, or finite-dynamical theorem support

```text
M1 M2 M3 M4 M5 M6B M7
E2 E3 E4 E5 E8 E9 E10 E11
E12 E13 E14 E16 E17 E18 E19 E20 E22 E28 E29 E32 E33 E36 E37 E38 E41
E45 E47 E49 E50 E51 E53
E57 E58 E59 E61 E62 E64 E72 E81
CLE4 CLE5 CLE8 CLE9 CLE10
G1 EX EY EZ FA
CM9 CM11
TOP3 TOP7
CORR2
```

This category includes conditional theorems, finite analogues, scalar reductions, exact algebraic bridges, counting lemmas, and quantitative error bounds. It does not imply full PDE, variational, continuum, or physical closure.

### Dimensional support

```text
E1A E1B E6 E7
```

### Definitions or model skeletons

```text
M6A E25 E27 E65 CM12 CM13 CM16
```

### Explicit analytic contracts or predicates

```text
M4 E24 E26 E66 E67 E68 E69 E70
```

The contracts expose missing Sobolev, regularity, interpolation, and stability hypotheses rather than assuming them silently.

### Counterexample or unresolved proposition support

```text
E17 E78
```

E17 includes both the historical scalar-denominator counterexample and the corrected complex denominator theorem. E78 remains a proposition/TODO rather than a completed Fisher-information theorem.

## Latest coverage expansion

### CORR2 — quantified weak-intermittency closure

`meanAmplitudeReciprocalFactor_band` proves that if a relative denominator fluctuation `δ` is trapped in `[-η,η]` with `0 ≤ η < 1`, then

```text
1/(1+η) ≤ 1/(1+δ) ≤ 1/(1-η).
```

Multiplying by the nonnegative mean spectral factor `k^4/Q_eff` gives the rigorous enclosure corresponding to the mean-amplitude closure. `meanAmplitudeReciprocal_upperError_exact` proves that the upper relative error factor is exactly

```text
η/(1-η).
```

Thus the closure error vanishes as the intermittency amplitude tends to zero. This does not assert that the local denominator actually satisfies the required uniform intermittency bound; that remains a model/analysis hypothesis.

### E32 — uniform alpha-drop margin

`alphaDrop_uniform_margin_bound` proves that the corrected E28 relation plus a uniform positive margin `β ≤ -A-δ`, `δ>0`, yields `α ≤ 1-δ`. `alphaDrop_uniform_margin_lt_one` then proves the strict pointwise tail inequality `α<1`. Applying the same margin on all sufficiently large indices supplies the algebraic core of the canonical `limsup α(n)<1` statement.

### E50 — phase-coherence finiteness core

`phaseCoherenceIntegrand_bound` proves the pointwise estimate

```text
0 ≤ density / |∇θ| ≤ density / δ
```

under nonnegative density and a positive floor `|∇θ| ≥ δ > 0`. For `density=|ψ|²` and `ψ∈L²`, integration gives the stated finite coherence bound. The Lean theorem formalizes the pointwise inequality; measurability and integration remain continuum assumptions.

### E41 and E72 — discrete retention counting

`iterated_count_retention_bound` proves that genuine nonnegative stepwise count-retention inequalities multiply through a finite sequence. `alphaFromRetentionLogSum_exponent_identity` proves the exact exponent bookkeeping connecting the retention product and E28 alpha definition. These theorems formalize the finite counting core; they do not independently establish that a physical WCT dynamics admits the required finite encoding.

### E19 — gap/mass consistency constraint

`gapCurvature_massSquared_chain` proves that a curvature-squared gap `Δω=c² C_gap σ²` inserted into the E49 mass relation gives

```text
m_eff² = C_gap (ℏ σ / c)².
```

`gapCurvature_unitCoefficient_recovers_massLawSquared` shows exact recovery of the squared E6 mass law at `C_gap=1`. This constrains the coefficient if the sectors are identified; it does not derive the spectral gap law itself.

### E22 — complex metric reality constraint

`complexMetricDerivativeEntry_hermitian` proves the raw complex derivative entry is Hermitian under index exchange. `complexMetricDerivativeEntry_not_symmetric_example` gives a concrete complex derivative pair for which the raw entries are not symmetric, while `complexMetricDerivativeEntry_realPart_symmetric` proves taking the real part restores symmetry. Nondegeneracy and Lorentzian signature remain separate obligations.

### TOP7 — curvature-energy diagnostic

`planarConstantCurvatureMass_squared` proves that in the torsion-free constant-curvature reduction,

```text
m² = (ℏ/c)² ε_κ
```

when `ε_κ=κ²`. This is a kernel-checked constraint showing that the canonical mass law naturally gives a squared-mass relation in that sector, not by itself a universal linear `m ∝ ε_κ` relation.

### CLE5 and CLE8 — flat-product torus selection

`flatProductTorusEigenvalue_nonnegative` proves nonnegativity of the integer Fourier-mode eigenvalue encoded as the sum of squared radius-scaled mode labels. For fixed winding/chirality `n = +1`, `flatProductTorus_fixedWinding_one_minimal` proves that the `m = 0` mode minimizes the flat-product eigenvalue, and `flatProductTorus_fixedWinding_one_eq_iff` proves that for nonzero major radius equality occurs only at integer `m = 0`.

These are exact statements for the flat-product torus spectrum. They do not prove that the full curved torus has the same spectrum without approximation, nor do they derive the physical winding/selection rule.

### TOP3 — exact negative-gradient-flow descent

`finiteGradientFlowEnergyRate_nonpositive` proves that the finite-dimensional exact negative-gradient-flow rate `-Σᵢ gᵢ²` is nonpositive. This is the algebraic core of the continuum identity `dE/dt = -||δE/δγ||² ≤ 0` under the differentiability and regularity hypotheses.

It does not establish well-posedness of the topology dynamics or differentiability of a singular self-avoidance functional.

### E16 — linearized spectral selection

`linearModePower_nonnegative` proves that nonnegative initial mode power stays nonnegative in the supplied exponential-growth model. `linearModePower_selects_larger_growth` proves that, for equal positive initial power and positive time, the mode with the larger supplied growth rate has strictly larger linearized power.

This is a linearized mode-selection theorem, not a proof of nonlinear global pattern selection.

### E37 and E38 — resource-scale algebra

`energyBandlimit_nonnegative` proves nonnegativity of the encoded energy-limited wavenumber scale under nonnegative coefficient/energy and positive `hbar,c`. `channelCapacityUpperBound_nonnegative` proves nonnegativity of the scalar channel-capacity upper-bound expression under nonnegative factors.

These results validate the encoded scalar structure; they do not derive the physical constants or prove the full computational-complexity interpretation.

### CM11 — Gaussian damping envelope

`curvatureDampingEnvelope_positive` proves strict positivity of the Gaussian envelope, while `curvatureDampingEnvelope_zero` proves exact zero-wavenumber normalization.

### CLE4, CLE9, and CLE10 — curvature-lock algebra

`curvatureLock_iff_lockedEigenEquation` proves, away from field zeros, equivalence between the scalar curvature quotient and the locked eigen-equation. `curvatureRadius_mul_curvature` proves the reciprocal radius identity for nonzero curvature. `curvatureScalarSq_iff_lockedEigenEquation` proves the corresponding squared-curvature eigen-equation equivalence.

These are scalar algebraic closures and do not prove existence or uniqueness of a toroidal electron solution.

## Earlier non-shallow mappings

### M4 — dimensional threshold

`h2Subcritical_iff_le_three` proves the integer arithmetic equivalence

```text
n < 4  ↔  n ≤ 3
```

while `SobolevCurvatureContract` keeps the actual embedding and curvature-boundedness obligations explicit.

### M5 and E36 — bounded averaged dynamics

`averagedUpdate_norm_le` proves norm nonincrease for convex mixing with a norm-nonexpansive local average. `averagedUpdate_preserves_normBound` proves forward invariance of the encoded bounded resource ball. `averagedUpdate_fixed_of_average_fixed` proves preservation of fixed points.

These are finite-dimensional update theorems, not complexity-class equivalences.

### M6B — nonlinear curvature operator

`thetaComplex_canonical_formula` proves that the typed complex operator is exactly

```text
(-Δψ · conjugate ψ) / (|ψ|² + ε² exp(-2 α |ψ|²))
```

after reassociation. `thetaComplex_denominator_ne_zero` supplies the positive-`ε` denominator condition.

This does not prove uniqueness of the nonlinear closure or PDE well-posedness.

### E10 and E11 — quantization closure

`radialShellQuantized_add` and `windingQuantized_add` prove closure under addition of phase integrals and integer indices. `radialShellQuantized_iff_windingQuantized` proves that the two predicates implement the same integer quantization law once the observable is fixed.

### E29 — entropy-pruning bound

Lean proves:

```text
0 ≤ K exp(-ΔH)
ΔH ≥ 0  →  K exp(-ΔH) ≤ K
ΔH₁ ≤ ΔH₂  →  K exp(-ΔH₂) ≤ K exp(-ΔH₁)
```

for nonnegative mode count `K`.

### G1 — bounded log-periodic ghost mode

`abs_ghostMode_le` proves that the modulation magnitude is bounded by the absolute amplitude.

### EX, EY, EZ, and FA — logarithmic-flow bridge

`exp_logField_eq` proves inversion of the logarithmic field on the positive sector. `coleHopf_residual_factorization` and `diffusionResidual_zero_iff_logCurvatureResidual_zero` prove the exact algebraic residual bridge under displayed temporal and Laplacian chain-rule hypotheses. `filamentLocalizationCondition_iff_mismatch_zero` characterizes localization as zero scalar mismatch.

These results do not supply the missing function-space chain rule or PDE regularity theorem.

## Layer 3 — Registry-only coverage: 62 IDs

The remaining 62 IDs compile with family and status metadata but do not yet have a maintained equation-specific typed declaration that captures substantive mathematical content.

Registry-only does **not** mean false. It means the object is inventoried and classified, but its formula or claim has not yet been represented beyond metadata in the maintained Lean library.

## Major compiled modules

| Module | Principal coverage |
|---|---|
| `WCTLean/Registry.lean` | all 142 IDs, families, effective statuses, completeness proofs |
| `WCTLean/Models/ComplexCurvature.lean` | M2, M6B, E17 corrected complex quotient and denominator safety |
| `WCTLean/Models/Locking.lean` | M1, E3, E4, E8 finite locking algebra |
| `WCTLean/Models/BandPass.lean` | M3, M7, E12, E57, E61, E64 finite-band algebra |
| `WCTLean/Models/PhaseFlux.lean` | E9, E10, E11 phase flux and additive quantization closure |
| `WCTLean/Models/AlgebraicChecks.lean` | E20, E28, E29, E33, E45, E47, E49, E51, E53, E59, E62, E81 |
| `WCTLean/Models/CoverageExpansion.lean` | E16, E32, E37, E38, E50, CLE4, CLE5, CLE8, CLE9, CLE10, CM11, TOP3, CORR2 theorem-level support |
| `WCTLean/Models/DerivedConstraints.lean` | E19, E22, E41, E72, TOP7 cross-equation and counting constraints |
| `WCTLean/Models/CompactDynamics.lean` | M5, E36 fixed points, norm nonincrease, bounded-set invariance |
| `WCTLean/Models/LogFlow.lean` | EX, EY, EZ, FA logarithmic and diffusion residual bridge |
| `WCTLean/Models/GhostModes.lean` | G1 bounded ghost-mode modulation and smearing definitions |
| `WCTLean/Contracts/Analytic.lean` | M4, E24–E27, E65–E70 analytic boundaries/contracts |
| `WCTLean/DerivedAudit.lean` | E5, E9, E13/E14, E18, E58, CM9, CM12, CM13, CM16 |
| `WCTLean/ResolvedAudit.lean` | E2, E3, E9, historical E17 counterexample |
| `WCTLean/Models/KoideDerivation.lean` | spin-dependent Koide algebra outside the canonical-ID count |
| `WCTLean/Models/Collider.lean` | collider log-coordinate and winding definitions |

## Status discipline

| Label | Meaning |
|---|---|
| `PROVED` | Lean accepts a theorem under its displayed hypotheses |
| `COUNTEREXAMPLE` | Lean proves a concrete failure of an unrestricted or historical claim |
| `CONDITIONAL` | named assumptions are required |
| `DEFINITION` | an object is introduced but no substantive property is proved |
| `CONTRACT` | an analytical requirement is represented explicitly as a hypothesis-bearing interface |
| `REGISTRY-ONLY` | ID, family, and status compile, but no equation-specific typed support is maintained |
| `TODO` / `OPEN` | no completed theorem closes the obligation |

A SymPy `PASS` must never be reported as a Lean proof. A Lean theorem must never be reported as empirical validation.

## Reproducibility

CI runs:

```bash
lake update
lake exe cache get
python scripts/audit_formal_sources.py
lake build
```

The audit rejects `sorry` and `admit`, verifies the public import closure, hashes every Lean source file, and confirms the pinned dependency graph remains unchanged.
