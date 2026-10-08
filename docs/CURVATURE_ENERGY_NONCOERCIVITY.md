# Counterexample: WCT curvature energy is not H²-coercive

**Status:** Exact analytic calculation. Only the algebraic frequency/curvature
bound is currently represented in Lean:
[`WCTLean/Models/OscillatoryNoncoercivity.lean`](../WCTLean/Models/OscillatoryNoncoercivity.lean).
No continuum Sobolev-integral theorem is claimed in Lean.

## Statement and model scope

Use the corrected WCT complex curvature operator from M2 / E17:

```math
\Theta_\varepsilon[\psi]
= -(\Delta\psi)\frac{\overline\psi}
  {|\psi|^2+\varepsilon^2\exp(-2\alpha|\psi|^2)}.
```

Take the special case `epsilon = 1`, `alpha = 0`, and the periodic
three-torus `Omega = (R/2pi Z)^3`, with volume `|Omega|=(2pi)^3`.
For any integer `N >= 1`, consider the real smooth field

```math
\psi_N(x_1,x_2,x_3)=N^{-1}\sin(N x_1).
```

Then

```math
\nabla\psi_N=(\cos(Nx_1),0,0),\qquad
\Delta\psi_N=-N\sin(Nx_1),
```

and the *corrected* curvature is exactly

```math
\Theta_1[\psi_N]
=\frac{\sin^2(Nx_1)}
        {1+N^{-2}\sin^2(Nx_1)}.
```

In particular, `0 <= Theta_1[psi_N] <= sin(Nx_1)^2 <= 1`.

## Uniform energy bound

The M2 energy candidate is

```math
\mathcal E[\psi]=
\int_\Omega (|\nabla\psi|^2+|\Theta_1[\psi]|^2)\,dx.
```

The elementary periodic integrals give

```math
\int_\Omega |\nabla\psi_N|^2\,dx
=\frac{|\Omega|}{2},\qquad
\int_\Omega |\Theta_1[\psi_N]|^2\,dx
\le \int_\Omega \sin^4(Nx_1)\,dx
=\frac{3|\Omega|}{8}.
```

Therefore `E[psi_N] <= 7|Omega|/8` for all `N >= 1`.

## Unbounded H² derivatives

Meanwhile,

```math
\|\partial_{x_1}^2\psi_N\|_{L^2(\Omega)}^2
=\frac{N^2|\Omega|}{2}\longrightarrow\infty.
```

Thus **there is no estimate**

```math
\|\psi\|_{H^2}\le F(\mathcal E[\psi])
```

for all smooth periodic fields with a locally bounded function `F`
(e.g. the usual `||psi||_{H²} <= C(E[psi]+1)` estimate).
More precisely, a uniform energy sublevel `E <= 7|Omega|/8` contains
functions with arbitrarily large `H²` norm.

## What this does and does not mean

- Proves that the *specified M2 energy functional*, on its own, does not
  control the full `H²` norm even in three dimensions.
- Does **not** exhibit a trajectory of an evolving WCT PDE, a singularity
  in finite time, or instability of an actual localized state.
- Does **not** disprove the separate projection-free Hamiltonian model in
  `wct-pde`; its Hamiltonian has a different leading fourth-order term.
- Does **not** contradict the standard implication
  `H²(Omega) -> L-infinity(Omega)` in dimension three.
  Rather, it shows why M2 energy boundedness alone cannot supply the
  premise of that embedding.

## Next proof obligation

For a *specified evolution and function space*, either prove a coercive
estimate using additional invariants/terms (e.g. explicit control of
`||Delta psi||_2`), or precisely characterize the restricted admissible
sector where such an estimate holds. Do not equate bounded M2 energy
with global regularity absent that estimate.
