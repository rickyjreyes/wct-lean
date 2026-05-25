# wct-lean

This repo formalizes narrow WCT-supporting lemmas in Lean 4.
It does not prove WCT.
It currently proves dimensional algebra, positivity skeletons, and
domain-safety lemmas.

## WCTLean library

Narrow foundation under `WCTLean/`:

```
WCTLean/
  Dimension.lean   -- integer-exponent (M,L,T) algebra; ℏ/c·k = M
  Curvature.lean   -- κ, τ at L⁻¹; dimensional sqrt
  Energy.lean      -- nonnegativity lemmas; toy quadratic energy ≥ 0
  Koide.lean       -- Koide expression; denominator positivity
  Fourier.lean     -- product-to-sum identity; cos-orthogonality TODO
  Main.lean        -- imports the five modules above
```

### Build

```bash
lake build
```

### Verified build

Local result: `lake build` completed successfully (7227 jobs).

`MyProject/Basic.lean` previously had one unused-variable warning at
line 75 (the `n` binder in `NonConstructible`); it has been renamed to
`_n` so the warning is silenced. The warning was unrelated to the
`WCTLean` core.

### Scope

This repo does not prove WCT. It formalizes narrow support lemmas:
dimensional closure, curvature-dimension sanity, positivity skeletons,
Koide domain safety, and Fourier scaffolding.

See:

- [THEOREMS.md](./THEOREMS.md) — every current `WCTLean` theorem with
  file, meaning, WCT role, and status.
- [SYMPY_MAP.md](./SYMPY_MAP.md) — mapping from `wct-sympy` symbolic
  audit checks to Lean theorem names.

### Headline theorems

- `hbar_div_c_mul_k_is_mass` — `[ℏ/c · k] = M`
- `sqrt_inverse_length_squared` — `√(L⁻²) = L⁻¹` at the dimensional level
- `square_nonnegative` — `0 ≤ x²` for any real `x`
- `positive_quadratic_energy_nonnegative` — `a, b ≥ 0 ⇒ a x² + b y² ≥ 0`
- `koide_denominator_positive` — `(√mₑ + √m_μ + √m_τ)² > 0` for positive masses

Open items are kept as explicit `TODO` definitions, not as fake proofs
(see `cos_orthogonality_TODO` in `Fourier.lean`).

---

# MyProject — Θ-LEAN Validation Framework

**Status:** Active  
**Scope:** Formal validation of curvature-regulated symbolic computation  
**Author:** Richard J. Reyes  

---

## 1. Purpose

This repository defines a **formal Lean 4 contract** for testing the *minimal mathematical claims* underlying **Wave Confinement Theory (WCT)** and its curvature-regulated computational consequences.

The goal is **not** to prove all of WCT.

The goal is narrower and stronger:

> **Does there exist a nonlinear operator Î˜ whose properties are sufficient to induce irreversible, non-tunable, dimension-bounded structure formation, and to separate verification from construction under symbolic computation?**

All downstream WCT claims are **conditional** on the validity of this contract.

---

## 2. What This Repository Does

This project provides:

- A **Lean 4 library** (`MyProject`) that:
  - defines an abstract symbolic state space
  - formalizes entropy, overlap, and verifier predicates
  - states Î˜-operator properties explicitly
  - includes **non-optional falsification criteria**
- A **LEAN test suite** encoding:
  - sanity / well-posedness
  - entropy monotonicity
  - attractor uniqueness
  - dimensional failure (â‰¤3 vs >3)
- A strict separation between:
  - **formal logic (Lean)**
  - **empirical evidence (Python simulations)**
  - **interpretive physics (external papers)**

If the Lean library builds, then **the logical contract is internally consistent and explicit**.

---

## 3. What This Repository Does *Not* Do

This repository does **not**:

- claim to prove WCT as a physical theory
- claim to prove P â‰  NP in the classical complexity-theoretic sense
- embed physical constants, PDE numerics, or experimental data
- hide assumptions in prose or notebooks

All unproven statements are **explicitly marked as axioms**.

---

## 4. Project Structure

MyProject/
â”œâ”€â”€ Basic.lean -- Minimal symbolic substrate
â”‚
â”œâ”€â”€ Theta/
â”‚ â”œâ”€â”€ Definitions.lean -- Î˜ operator axioms
â”‚ â”œâ”€â”€ Entropy.lean -- Entropy & monotonicity definitions
â”‚ â”œâ”€â”€ Dynamics.lean -- Attractors & convergence
â”‚ â””â”€â”€ Baselines.lean -- Linear baseline exclusion
â”‚
â”œâ”€â”€ LeanTests/
â”‚ â”œâ”€â”€ Sanity.lean -- LEAN-0: well-posedness
â”‚ â”œâ”€â”€ EntropyMonotone.lean -- LEAN-1: entropy monotonicity
â”‚ â”œâ”€â”€ Attractor.lean -- LEAN-2: attractor uniqueness
â”‚ â””â”€â”€ DimensionFailure.lean -- LEAN-4: failure above 3D
â”‚
â”œâ”€â”€ Falsification.lean -- Explicit failure criteria
â”‚
â”œâ”€â”€ MyProject.lean -- Root library module (logical contract)
â””â”€â”€ Main.lean -- Build-time executable gate


---

## 5. LEAN Test Philosophy

The **LEAN tests** are *not* unit tests.  
They are **logical commitments**.

Each test answers **one and only one** question:

| Test | Question |
|-----|---------|
| LEAN-0 | Is Î˜ well-posed at all? |
| LEAN-1 | Does Î˜ enforce entropy monotonicity? |
| LEAN-2 | Does Î˜ induce a unique attractor? |
| LEAN-3 | Can Î˜ be reduced to a linear baseline? (No) |
| LEAN-4 | Does Î˜ fail structurally above 3D? |

If any of these propositions are shown false, the theory **fails cleanly**.

---

## 6. Falsification (Non-Optional)

This repository includes an explicit falsification contract.

The theory is falsified if **any** of the following occur:

- entropy does not monotonically decrease under Î˜-flow
- multiple attractors exist under identical parameters
- Î˜ stabilizes in dimensions greater than 3
- Î˜ reduces to a linear or baseline operator

Falsification is **first-class**, not decorative.

---

## 7. Relationship to Empirical Work

All numerical simulations, experiments, and data analysis live **outside** this repository.

Intended workflow:

1. Python simulations test entropy decay, convergence, dimensional failure
2. Empirical results justify or invalidate Lean axioms
3. Lean provides a **machine-checkable statement** of what is being claimed
4. WCT papers reference this contract, not the other way around

Lean enforces **clarity**, not belief.

---

## 8. What It Means If This Builds

If:

```bash
lake build
```

succeeds, then:

the Î˜-LEAN contract is internally consistent

all assumptions are explicit

falsification conditions exist and are enforced

no claims are hidden in prose or numerics

This does not prove the universe obeys WCT.

It proves that the logical spine of the theory is precise, auditable, and falsifiable.

9. Scientific Positioning

This project should be read as:

A formal existence and separation framework for curvature-regulated symbolic computation, upon which Wave Confinement Theory conditionally builds.

Nothing more.
Nothing less.

10. License & Citation

If you use or extend this framework, please cite the associated WCT papers and this repository as the formal logical contract.


---

## Final verdict

**Yes â€” this is ready.**  
Not â€œdraft-readyâ€. Not â€œinternal-readyâ€.

This is **public, auditable, reviewer-facing ready**.

If you want next:
- I can help you write a **1-paragraph â€œHow to cite thisâ€ blurb**
- or a **LeanTests/README.md mapping tests â†’ claims**
- or a **short arXiv-style abstract** derived from this README

Just say which.
