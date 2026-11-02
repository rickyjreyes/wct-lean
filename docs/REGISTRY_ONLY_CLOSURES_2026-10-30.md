# Exact mathematical closures for formerly registry-only WCT entries

**Source baseline:** [corrected canonical registry](https://github.com/rickyjreyes/geometry_of_resonance/blob/main/WCT_FULL_EQUATION_LIST_CORRECTED.md) (revision 2.0)  
**Lean module:** [RegistryOnlyClosures.lean](../WCTLean/Models/RegistryOnlyClosures.lean)  
**Purpose:** supply rigorous, narrow proofs and counterexamples without promoting unresolved physical claims.

## New Lean targets

| Registry ID | Exact result represented | Interpretation | Remaining work |
| --- | --- | --- | --- |
| TOP6 | `top6_statistic_scales_inverse_square`, `top6_dilation_changes_statistic` | Scaling obstruction to **unrestricted** disjoint curvature bands | Geometric immersion/isotopy formalization, fixed-length or scale-invariant replacements, empirical spectral data |
| CM3 | `cm3_potential_poisson_relation` | Algebraic Fourier-space potential consistency at nonzero k | Constitutive derivation, zero-mode handling and governing PDE |
| CM4 | `cm4_decay_iff_nonpositive_logarithmic_rate` | Exact real logarithmic-rate compatibility criterion | Complex rates, variable coefficients, horizon physics |
| CM10 | `cm10_drag_contracts_difference` | Convex discrete drag contracts baryon/photon mismatch | Derive drag coefficient and coupling evolution |
| CM15 / CM20 | `cm15_cm20_compatible_iff_energy_loss` | Exact necessary/sufficient scalar compatibility condition | Full derivative theorem, energy closure, observational comparison |
| E44 | `e44_local_curvature_global_phase_invariance`, `e44_phase_rotated_eigenvalue_obstruction` | Global-phase-invariant curvature operator is **not** generally a complex-linear eigenoperator | Nonlinear spectral problem, normalization, admissible symmetry breaking |
| E60 | `e60_real_squared_amplitude_derivative`, `e60_real_stationary_iff` | Real scalar amplitude ODE and stationary state classification | Full center-manifold reduction and PDE error bounds |
| E82 | `e82_information_gram_symmetric`, `e82_information_gram_diagonal_nonnegative`, `e82_information_gram_quadratic_nonnegative` | Finite real feature-space Gram tensor and sum-of-squares positivity | Function-space differentiability and coordinate invariance |

### TOP6: analytic geometric obstruction

For a smooth immersed closed curve of length `L > 0`, let
`B = ∫_γ κ² ds` and `ε_κ = B/L`. Under the similarity dilation
`γ ↦ aγ` for `a > 0`,

```text
L(aγ) = a L(γ)
κ(aγ) = κ(γ)/a
B(aγ) = B(γ)/a
ε_κ(aγ) = ε_κ(γ)/a².
```

Positive similarity dilation preserves the ambient isotopy (knot) class:
interpolate continuously through strictly positive scale factors.
For every closed regular curve, `B > 0`. Given any target `q > 0`,
choose `a = sqrt(ε_κ(γ)/q)`, obtaining `ε_κ(aγ) = q`.
**Consequently every knot class that admits a smooth embedded
representative attains the same entire positive range of this
unnormalized statistic across unrestricted dilations.**
This refutes the claim that *disjoint topology bands arise from this
single unnormalized scalar on unrestricted scales*. It does **not**
refute possible discrimination using scale-normalized quantities,
multiple spectral invariants, or an explicitly constrained size/energy
class.

The Lean module checks the quantitative scalar scaling law and a
strict 2×-dilation change; the geometric curvature-transformation and
ambient-isotopy facts in this paragraph are analytic, **not yet Lean
theorems**.

### CM3 and CM4: analytic compatibility

Fix real, constant nonzero `a = -C_Φ/k²`, with `k ≠ 0`, and a
real differentiable nonvanishing mode `Θ`. Then
`Φ = a Θ` implies `Φ' = a Θ'`. Write `r = Θ'/Θ`.
CM4 prescribes `Φ' = -|r|Φ`, so

```text
a r Θ = -|r| a Θ   iff   r = -|r|   iff   r ≤ 0.
```

Hence the stated CM3 and CM4 formulas are mutually compatible
**exactly for nonincreasing real logarithmic curvature rates**.
A growing mode `Θ(t) = exp(t)` provides an explicit incompatible
case. For complex Θ the necessary condition is stronger:
`Θ'/Θ` must lie on the nonpositive real axis.
The Lean theorem handles the fully quantified real scalar reduction.

### CM10: discrete drag contraction

For `0 ≤ ε ≤ 1`, the drag map
`b' = (1-ε)b + εg` with fixed comparison state `g`
satisfies

```text
|b' - g| = (1-ε)|b-g| ≤ |b-g|.
```

At `ε > 0`, the contraction is strict whenever `b ≠ g`.
This is a discrete algebraic statement, not a proof of a
time-dependent coupled photon/baryon cosmology.

### CM15 and CM20: expansion closure

For differentiable positive curvature energy `E(t)`, with
`E(0) > 0`, CM15 defines
`a(t) = [E(0)/E(t)]^(1/3)`.
Ordinary logarithmic differentiation yields

```text
H(t) = a'(t)/a(t) = -E'(t)/(3 E(t)).
```

For `K ≠ 0` and `ρ_Θ ≥ 0`, equality with the nonnegative
CM20 ansatz `H(t)=sqrt[ρ_Θ/(3|K|)]` is equivalent to

```text
E'(t) = -3 E(t) sqrt[ρ_Θ(t)/(3|K|)].
```

The Lean theorem proves this necessary/sufficient algebraic
compatibility condition for supplied nonzero energy and instantaneous
derivative data. It does not prove the preceding differential chain
rule or derive the physical density `ρ_Θ`.

### E44: nonlinear curvature and global phase

The canonical corrected curvature operator is
`Θ_ε[ψ] = -Δψ conjugate(ψ)/D_ε(ψ)`, where
`D_ε(ψ)=|ψ|²+ε² exp(-2α|ψ|²)`.
For a constant `u∈ℂ` of modulus one, `Δ(uψ)=uΔψ`,
`D_ε(uψ)=D_ε(ψ)`, and `u conjugate(u)=1`, so
`Θ_ε[uψ]=Θ_ε[ψ]`.

However, the registry's nonlinear eigenmode equation reads
`Θ_ε[ψ]=λψ`. If both `ψ` and `uψ` are supposed to solve it
with the **same** eigenvalue and `u≠1`, phase invariance forces
`λψ=0`. The covariance expected of a linear eigenoperator does
not hold automatically. The Lean module proves the phase-cancellation
identity for a shared invariant denominator and the eigenmode
obstruction. It does **not** classify nonlinear eigenmodes.

### E60: real amplitude closure

For the *specified real scalar reduced equation*
`A' = μA-gA³`, define `y=A²`. Then

```text
y' = 2μy - 2gy²
0 = μA-gA³   iff   A=0 or μ=gA².
```

If `μ>0`, `g>0`, and `y(0)>0`, the logistic solution is
`y(t)=(μ/g)/[1+(μ/(g y(0))-1)e^(-2μt)]`, converging to `μ/g`.
Lean proves the derivative identity and stationary factorization.
The explicit solution and asymptotic convergence in this paragraph
are analytic calculations, not yet formalized.

### E82: finite information geometry

Let `A_{ik}` be real feature derivatives and set
`g_{ij}=Σ_k A_{ik} A_{jk}`. Then

```text
g_ij = g_ji
Σ_ij v_i g_ij v_j = Σ_k (Σ_i v_i A_ik)² ≥ 0.
```

This proves symmetric positive semidefiniteness for the
finite-dimensional real Gram construction. Positive definiteness
requires the feature derivative map to be injective on parameter
directions. Lean proves symmetry, diagonal nonnegativity, and
nonnegativity of the sum-of-squares quadratic representation;
the explicit double-sum matrix identity in this paragraph remains
a paper-level algebraic calculation.

## Existing related proof sources, not duplicated here

* **E15, CLE6, CLE7:** [`NarrowCanonicalCoverage.lean`](../WCTLean/Models/NarrowCanonicalCoverage.lean) already contains their narrow real-mode/quotient/periodicity results. It does not yet prove the full CLE7 ODE completeness theorem.
* **E21:** [math: elementary compendium §5](https://github.com/rickyjreyes/math/blob/main/compendium/wct-elementary-mathematics/main.tex) contains the analytical generalized Euler–Lagrange derivation.
* **E30:** [math: elementary compendium §3](https://github.com/rickyjreyes/math/blob/main/compendium/wct-elementary-mathematics/main.tex) proves `0 ≤ H(P) ≤ ln K`, with the equality conditions, for finite discrete distributions.
* **CLE6 and CLE7:** [same compendium §6](https://github.com/rickyjreyes/math/blob/main/compendium/wct-elementary-mathematics/main.tex) gives the classical flat-product separation and periodic angular-mode proofs.
* **E18 and E69:** separate [analytical manuscripts](https://github.com/rickyjreyes/math/blob/main/CONTENTS.md) address negative-gradient-flow dissipation and high-regularity curvature bounds, not the full physical curvature-flow and information-decay claims.

## Status and verification contract

* **Typed support** means an equation has an explicit non-registry Lean definition or theorem.
* **Kernel checked** requires a successful pinned Mathlib / Lean build; source submission alone is insufficient.
* **Analytical closure** is narrower than experimental validation, and a Lean proof of a reduced model does not change a canonical physical `OPEN` claim.
* Preserve the canonical *symbolic/physical* status for TOP6, CM3, CM4, CM10, CM15, CM20, E44, E60 and E82 until the source-of-truth audit justifies a change. In particular TOP6 remains open as a **constrained/normalized topology classification** after its unrestricted scalar-band obstruction is established.

To check these files:

```bash
python scripts/audit_formal_sources.py
lake build WCTLean.Models.RegistryOnlyClosures
lake build
```
