# Proof backlog status (resumable record)

Branch: `claude/wonderful-turing-3no9vg` (based on `main` at `5c784f7`).
Toolchain: `leanprover/lean4:v4.23.0`, Mathlib `v4.23.0` (pinned in
`lakefile.lean` / `lake-manifest.json`).

Model scopes are kept distinct throughout:

- **finite-dimensional** — algebraic or finite-mode statements;
- **periodic / one-dimensional PDE models** — `[0, 2π]`, `AddCircle T`;
- **whole-space WCT** — not reached by anything on this branch.

## How to resume

```bash
lake exe cache get
python3 scripts/audit_formal_sources.py
lake build
lake env lean scripts/fourier_e78_axiom_audit.lean > fourier-e78-axioms.log
python3 scripts/check_axiom_log.py fourier-e78-axioms.log 44 "Fourier/E78"
lake env lean scripts/curvature_nodal_energy_axiom_audit.lean > nodal.log
python3 scripts/check_axiom_log.py nodal.log 12 "nodal-energy"
lake env lean scripts/closure_classification_axiom_audit.lean > cc.log
python3 scripts/check_axiom_log.py cc.log 17 "closure-classification"
lake env lean scripts/curve_locking_axiom_audit.lean > cl.log
python3 scripts/check_axiom_log.py cl.log 15 "curve-locking"
lake env lean scripts/m7_linear_semigroup_axiom_audit.lean > m7.log
python3 scripts/check_axiom_log.py m7.log 18 "m7-linear-semigroup"
```

Hosted CI runs only on `pull_request` and pushes to `main`; this branch has
been verified locally with the pinned toolchain (full `lake build`, source
audit, all existing and new axiom audits).

## Status by issue (priority order)

### #23 — Fourier orthogonality, spectral projection, E78 — CLOSED for the periodic model

Done on this branch (56 audited roots across #23/#22 modules; see `THEOREMS.md`):

- `WCTLean/Fourier.lean`: cos/cos, sin/sin, sin/cos orthogonality and
  normalization on `[0, 2π]`; integer cosine Gram matrix. The historical
  `cos_orthogonality_TODO` is **false** and refuted
  (`cos_orthogonality_TODO_false`, `n = 1`, `m = -1`).
- `WCTLean/FourierSpectral.lean`: `L²(AddCircle T)` finite spectral projection
  = orthogonal projection; idempotence, self-adjointness, Parseval, Bessel,
  best approximation; `P_S f → f`, symmetric partial sums, Parseval in norm
  form; band-limited multipliers; M3/M7 and E12 symbols lifted to `L²`
  energy bounds.
- `WCTLean/Models/FisherCurvature.lean` (E78): printed universal inequality
  refuted for the maintained `thetaComplex` (every `ε`, every `α ≥ 0`, every
  `c > 0`); exact identity `I_F = 4∫Re Θ_ε·D_ε = 4∫(ψ')²`; reverse inequality
  `I_F² ≤ 16(∫D_ε²)(∫|Θ_ε|²)`.

Remaining (outside issue scope): whole-space/curved-domain spectral theory;
complex fields with nontrivial phase in the E78 identity (expected:
`I_F ≤ 4∫|ψ'|²` with equality iff the phase is locally constant). Registry
keeps E78 in `openIds` because the printed statement is false; a registry
"refuted" status would need a maintainer decision.

### #22 — regularized curvature quotient as ε → 0 — PARTIAL (new nodal dichotomy)

Main had: fixed-field pointwise limits (`ComplexCurvatureLimit.lean`).
Unmerged draft stack (#43 → #47 → #48 → #49 → #52 → #54): quantitative
gap-dependent bounds, Lp limits, no-gap majorants, conditional dominated
convergence, multiplicative-Laplacian Lp bounds, pointwise-jet obstruction.

New on this branch (`WCTLean/Models/CurvatureNodalEnergy.lean`, genuine
`C²` fields on the 1D model):

- `nodal_curvature_energy_lower_bound`: at a simple node with `ψ'' ≠ 0`,
  `∫_{x₀-ε}^{x₀+ε}|Θ_ε|² ≥ C/ε`;
- `nodal_curvature_energy_tendsto_atTop`, periodic witness
  `cos_sub_half_curvature_energy_tendsto_atTop`: energy → +∞;
- `curvature_energy_tendsto_of_multiplicative`, `sin_curvature_energy_tendsto`:
  convergence to `∫V²` when `ψ'' = Vψ` and nodes are null.

This shows the integrable-quotient hypothesis of the draft stack *fails* for
every field with a simple node carrying nonzero Laplacian.

Next concrete targets:

1. weak (distributional) limit at a simple node — expected principal value
   `-(ψ''(x₀)/ψ'(x₀)) p.v. 1/(x - x₀)` locally; would show weak convergence
   survives where energy diverges;
2. 2D vortex nodes: logarithmic energy divergence `~ log(1/ε)` when `Δψ ≠ 0`
   at the vortex core;
3. nodes of actual WCT evolution trajectories (needs #19).

### #26 — uniqueness/non-uniqueness of the curvature closure — RESOLVED at operator-selection level

Main: `m6bInfinitelyManyClosures` (explicit infinite family). Draft stack
#50 → #51 → #53: selection anchor, common ε→0 limit, global-U(1) invariance.

New on this branch (`WCTLean/Models/ClosureClassification.lean`, 17 roots):

- precise admissible class: `LaplacianHomogeneous`, `PhaseInvariant`,
  `AdmissibleRegularizer` (node-safe positivity, off-node limit,
  `UnitCovariant`);
- `closure_classification`: structural class = radial reweightings
  `-(Δψψ̄)g(|ψ|²)`;
- admissible regularizers ⇔ profiles `Φ > 0`, `Φ(u)/u → 1`
  (`admissible_profile`, `admissible_profile_asymptotic`,
  `profileRegularizer_admissible`) ⇒ **non-unique**
  (`admissible_closures_infinite`);
- maintained fixed-`α ≠ 0` regularizer is *not* unit covariant;
  `α = a/ε²` is admissible;
- uniqueness ⇔ two explicit extra principles (affine profile, `D_ε(0) = ε²`)
  ⇒ `thetaComplex` with `α = 0` (`closure_unique_affine_normalized`); the two
  principles are independent (`extra_principles_independent`).

Remaining: an *action-level* derivation of either extra principle (no
variational principle in the repository currently selects `Φ`); closures
depending on derivatives of `ψ` beyond `(ψ, Δψ)`; local (gauge) covariance.

### #19 — nonlinear well-posedness — PARTIAL (linear part done)

Draft PR #37 (pinned MathProofs dependency) has M7 symbol and Lipschitz
estimates. New on this branch (`WCTLean/Models/M7LinearSemigroup.lean`,
18 roots): the *linear* M7 flow on `L²(AddCircle T)` is globally well posed
(evolution operator, semigroup law, `e^{Ct}` bound, Lipschitz dependence,
strong continuity, existence and uniqueness of Fourier-mild solutions).

Next concrete targets: (1) `L² → H²` smoothing `‖Δ S(t) f‖ ≲ t^{-1/2}‖f‖`
from the quartic symbol (PR #37 has the multiplier-level estimate);
(2) Duhamel fixed point for the nonlinear curvature term in
`C([0,T]; H²(AddCircle))`, which needs the `H²` space as a weighted `ℓ²`
subspace and the Lipschitz bound of `N_curv` (PR #37). No nonlinear
statement is proved on this branch.

### #20 — free-space existence/localization/decay — OPEN

D4 Phase VI conditional chain on main. Needs concentration compactness;
not attempted on this branch.

### #21 — linearized spectrum and orbital stability — PARTIAL (trivial state, periodic model)

New on this branch: around the trivial state the linearized M7 /
Swift–Hohenberg flow has the Fourier modes as eigenmodes
(`evolution_fourierMode`); exponential stability when the symbol is
`≤ -γ` and unbounded modal growth when a symbol value is positive
(`evolution_exponentially_stable`, `evolution_mode_unbounded`,
`swiftHohenberg_shell_unstable`, `swiftHohenberg_subcritical_stable`).

Remaining: linearization around nontrivial confined states, symmetry
quotient, orbital/Lyapunov stability (D4 handoff in the issue body).

### #24 — curve-integral locking on manifolds — CLOSED for C¹ loops on open subsets of real normed spaces

New on this branch (`WCTLean/Models/CurveLocking.lean`, 15 roots): integer
winding of `∮ dψ/ψ` for every `C¹` nonvanishing closed loop
(`winding_quantized`, `field_loop_winding_quantized`); E11 predicate derived
from geometry; local polar identity vs global obstruction (every integer
occurs); E11 additivity from products; E4 locking constant determined by the
geometric winding.

Remaining: homotopy invariance of the winding; loops on manifolds beyond
Euclidean chart domains (Mathlib `ContMDiff` setting); E10 radial-shell
instantiation from an explicit radial phase field.

### #25 — physical observable bridges — OPEN (blocked on upstream existence results)

### #28 — remaining continuum obligations — OPEN

## Change log

- Commit `57b1906`: #23 Fourier/spectral/E78 (44 audited roots).
- Commit `bbfd270`: #22 nodal energy dichotomy (12 audited roots) + this record.
- Commit `254bd38`: #26 closure classification (17 audited roots).
- Commit `d7fd8a6`: #24 curve-integral locking (15 audited roots).
- Next commit: #19/#21 linear M7 semigroup (18 audited roots).
