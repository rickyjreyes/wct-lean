# Continuum issues #19–#21: theorem-level verification ledger

Source baseline: `wct-lean` main `1b281271caf84495b41ad93e775b9570db626302`.
Reused formal source: `math` SHA `afa8c27db10e9eff54f4dbb3e8e2d9530d042542`, package root `lean/`.
Toolchain and Mathlib: 4.23.0.

## Model separation

**Independent CQ:** `H²(ℝ²;ℂ)` is the weak/Schwartz-closure space
`ReyesMath.Sobolev.H2 2`. `M`, `energy` and `Imin` are the imported
genuine mass, fourth-order Hamiltonian and mass-constrained infimum. WCT Lean's
`mass`, `energy` and `constrainedInfimum` abbreviations are definitionally
identical, so no approximation or unstated equivalence is introduced.

**Corrected WCT:** `WCTLean.thetaComplex` is
`-lapPsi * conj(psi) / (|psi|² + ε² exp(-2α|psi|²))`. Positive denominator
does not prove quasilinear PDE existence, conservation, or coercivity.

**Periodic D4:** The root of `(Δ+1)²u − β|u|²u + γ|u|⁴u` on the 42-periodic
two-torus is not identified with a translated ℝ² minimizer. D4 denotes square
symmetry, not spatial dimension four.

## Exact frozen values

`β=γ=4608178181141995/1125899906842624`,
`m=1432536998431173/562949953421312`, `k=1`.
`ReyesMath.StrictBinding.frozen_parameters` establishes
`m < mB β β 1`; this is a **sufficient whole-space binding criterion**.

## Claim-to-Lean declaration map

| Issue | Model / scope | Exported declaration | Proof provenance | Status |
|---|---|---|---|---|
| #19 | Corrected M2/E17 quotient nodal vanishing and no globally positive coefficient floor | `WCTLean.Continuum.corrected_curvature_vanishes_at_field_node`, `WCTLean.Continuum.no_positive_uniform_quotient_coefficient_lower_bound` | direct corrected-model proof, no PDE well-posedness claim | Check CI |
| #20 (positive corrected curvature candidate) | Exact whole-plane zero infimum, nonattainment and local constrained no-minimizer on complex H² | `WCTLean.Continuum.canonical_positive_energy_infimum_zero`, `WCTLean.Continuum.canonical_positive_energy_nonattainment`, `WCTLean.Continuum.canonical_positive_energy_no_local_minimizer` | `ReyesMath.Curvature.global_nonattainment` and `.no_local_minimizer` with c₁=c₂=1 and d=2 | Check CI |
| #20 | Definitional weak H² model agreement | `WCTLean.Continuum.model_correspondence` | direct definitional proof | Check CI |
| #20 | Whole-plane prescribed mass and minimizer | `WCTLean.Continuum.exists_free_space_minimizer` | `ReyesMath.WholeSpace.exists_minimizer` | Check CI |
| #20 | Existence of a nonzero L² field | `WCTLean.Continuum.exists_nonzero_minimizer` | minimizer + positive mass | Check CI |
| #20 | Strong H² subsequential compactness modulo translations | `WCTLean.Continuum.free_space_minimizing_sequences_compact` | `ReyesMath.WholeSpace.compactness` | Check CI |
| #20 | Exact symmetry invariance of mass and energy | `WCTLean.Continuum.free_space_translation_invariant` | `H2.M_translate`, `H2.energy_translate` | Check CI |
| #20 | Exact frozen mass threshold and existence | `WCTLean.Continuum.frozen_whole_plane_existence` | `StrictBinding.frozen_parameters` + attainment | Check CI |
| #19 (separate model) | Global complex CQ H² evolution | `WCTLean.Continuum.independent_global_flow` | `ReyesMath.OrbitalStability.global_flow` | Check CI |
| #21 | Arbitrary-complex pointwise cubic/quintic expansion and exact first-order terms | `WCTLean.Continuum.cubic_exact_expansion`, `WCTLean.Continuum.quintic_exact_expansion`, `WCTLean.Continuum.cubicQuinticPotential_eq` | polynomial identities, no spectrum claim | Check CI |
| #21 (separate model) | Full-set CQ orbital stability | `WCTLean.Continuum.independent_orbital_stability` | `ReyesMath.OrbitalStability.orbital_stability` | Check CI |
| #21 (separate model) | Frozen-parameter CQ whole-plane stability | `WCTLean.Continuum.frozen_whole_plane_orbital_stability` | threshold + global CQ orbit theorem | Check CI |

## Acceptance verdicts

- **#19 PARTIAL**: Independent CQ evolution is imported as a comparison theorem.
  The *corrected curvature PDE* remains without a proved evolution generator,
  Banach-space local Lipschitz/quasilinear estimate, existence, or continuation
  theorem. No equation-level WCT well-posedness is claimed.
- **#20 PARTIAL**: Whole-plane existence, mass/finite energy, nonzero state,
  translated compactness, and exact frozen parameter instantiation are present
  for the *independent* CQ model, once CI passes. A separate explicit spatial
  tail theorem and stronger pointwise/exponential decay have not been exported;
  the positive corrected-curvature energy's constrained minimizers are absent under the stated positive-coefficient assumptions. Other canonical confinement mechanisms remain open.
- **#21 PARTIAL**: Independent whole-plane CQ orbital stability under general
  complex perturbations is imported. Periodic D4 root validation, its actual
  real-linearized operator and neutral-mode quotient, inverse/tail certificates,
  constrained spectral gap, and concrete periodic-root stability remain open.

## Integrity and required final verification

Run `lake update`, `lake exe cache get`, `lake build` from repository root.
Run `lake build WCTLean.Continuum.CubicQuinticWholeSpace`, source audit,
`#print axioms` and the CI workflows at the exact PR head.
No statuses in this report imply local build or GitHub CI passed before
those runs finish. Do not merge or close any issues from this ledger alone.

The independent cubic–quintic pointwise nonlinearity is also represented in `WCTLean/Continuum/CubicQuinticLinearization.lean`: its exact real-linear algebraic terms and higher-order remainders are proved for arbitrary complex perturbations. These polynomial identities do not by themselves establish a Fréchet derivative on the torus's unbounded operator domain or the D4 spectral gap.

The corrected M2/E17 curvature quotient has an additional exact pointwise limitation: `WCTLean.Continuum.no_positive_uniform_quotient_coefficient_lower_bound` rules out any strictly positive global lower bound on the modulus of the quotient's Laplacian coefficient, because it vanishes at field nodes. This is **not** a theorem of failure of uniform ellipticity for the complete governing PDE, let alone ill-posedness or finite-time blow-up.

### Positive canonical curvature-energy obstruction (#20)

The positive corrected-curvature candidate `E(u) = K(u) + Wc(ε,α,u)`,
on `H²(ℝ²; ℂ)`, has an exact constrained infimum zero **without any
attaining minimizer** when ε>0, α≥0 and mass m>0. Indeed no mass-m field
is even a local constrained minimum: arbitrarily small H² neighborhoods
contain an equal-mass lower-energy dilation. These are instantiated
whole-space theorems from the pinned `MathProofs.CurvatureNonattainment`,
not a no-go theorem for all canonical WCT dynamics or nonvariational
localized solutions. They directly rule out this specific **positive-energy
constrained-minimization route** to intrinsic confinement.

Exact exported declarations:
`WCTLean.Continuum.canonical_positive_energy_infimum_zero`,
`WCTLean.Continuum.canonical_positive_energy_nonattainment`,
`WCTLean.Continuum.canonical_positive_energy_no_local_minimizer`.

