# Wave Confinement Theory â€” Canonical Equation Families (E1â€“E82)

**Richard J. Reyes â€” Master Reference (v1.0, Nov 2025)**

This document is the authoritative catalogue of the core equations used across the WCT research volumes. Each entry contains: (i) plain definition, (ii) symbolic form, (iii) context (paper/module).


---

## 0. Symbol Table

| Symbol | Definition |
|--------|------------|
| $\psi(x,t)$ | Wavefield (complex) |
| $\Theta[\psi]$ | Curvature-feedback operator |
| $\kappa, \tau$ | Curvature, torsion of loop |
| $\sigma_{\text{dens}}(s) = \kappa(s)^2 + \tau(s)^2$ | Curvature-rate density along $\Gamma$ (units $L^{-2}$) |
| $\sigma(s) = \sqrt{\kappa(s)^2 + \tau(s)^2}$ | Curvature spectral rate (inverse-length scale, units $L^{-1}$) |
| $w(s)$ | Energy-density weight along loop |
| $A(x,t)$ | Band-pass amplitude |
| $\hat{A}_k$ | Fourier mode of $A$ |
| $H_k$ | Spectral entropy |
| $\mathcal{E}[\psi]$ | WCT Lyapunov functional |
| $\Lambda$ | Winding-number Lagrange multiplier |
| $k_{\text{eff}}$ | Effective wavenumber |
| $\alpha(n)$ | $\alpha$-Drop exponent |
| $U$ | Discrete WCC update rule |
| $k_{\max}$ | Energy-limited bandlimit |
| $N_{\text{lanes}}$ | Spatial channel capacity (modes/lanes) |

---

## A. Rest Energy, Curvature, Loop Locking

*(Rest Energy / Solenoidal Mass)*

### E1a â€” Curvature-rate density

Curvature-plus-torsion density along a loop $\Gamma$:

$$\sigma_{\text{dens}}(s) = \kappa(s)^2 + \tau(s)^2$$

---

### E1b â€” Curvature spectral rate (inverse-length)

Inverse-length curvature scale used for locking / effective wavenumber:

$$\sigma(s) = \sqrt{\kappa(s)^2 + \tau(s)^2}$$

---

### E2 â€” Weighted loop average

Density-weighted average of a scalar $f$ along $\Gamma$:

$$\langle f \rangle_w = \frac{\oint_\Gamma w(s)\, f(s)\, ds}{\oint_\Gamma w(s)\, ds}$$

---

### E3 â€” Loop-locking action

Phaseâ€“curvature locking with winding constraint:

$$S_{\text{eff}}[\varphi] = \oint_\Gamma w(s) \left(\partial_s \varphi(s) - \sigma(s)\right)^2 ds + \Lambda \left( \oint_\Gamma \partial_s \varphi(s)\, ds - 2\pi n \right)$$

---

### E4 â€” Covariant locking (Eulerâ€“Lagrange)

Phase gradient with density correction:

$$\partial_s \varphi(s) = \sigma(s) + \frac{\alpha}{w(s)}$$

where

$$\alpha = \frac{2\pi n - \oint_\Gamma \sigma(s)\, ds}{\oint_\Gamma \frac{ds}{w(s)}}$$

---

### E5 â€” Effective wavenumber identity

Equivalence of winding, loop-length, and curvature average:

$$k_{\text{eff}} = \frac{2\pi|n|}{L_s} = \frac{1}{L_s} \oint_\Gamma \sigma(s)\, ds = \langle\sigma\rangle_w$$

where $L_s := \oint_\Gamma ds$

---

### E6 â€” Massâ€“curvature law

Rest energy and mass from effective curvature:

$$E_{\text{rest}} = \hbar c\, k_{\text{eff}}$$

$$m = \frac{\hbar}{c} \langle\sigma\rangle_w$$


---

### E7 â€” Solenoidal mass law

Mass from curvatureâ€“torsion combination along $\Gamma$:

$$m = \frac{\hbar}{c} \left\langle \sqrt{\kappa^2 + \tau^2} \right\rangle_\Gamma$$

---

### E8 â€” Density-weighted lock identity

Integral identity for a locked loop:

$$\oint_\Gamma w\, \partial_s \varphi\, ds = \oint_\Gamma w\, \sigma\, ds + \frac{2\pi\alpha \oint_\Gamma ds}{\oint_\Gamma \frac{ds}{w(s)}}$$

---

## B. Phaseâ€“Flux Field & Cymatic Rails

### E9 â€” Phaseâ€“flux constitutive axiom

Phase flux proportional to amplitude:

$$\mathbf{S}(x,t) = u(x,t)\, \nabla\theta(x,t)$$

---

### E10 â€” Radial shell quantization

Radial wavenumber quantization between shells:

$$\int_{r_1}^{r_2} k_r(r)\, dr = 2\pi n$$

---

### E11 â€” PFF vorticity

Topological phase winding number:

$$m(\gamma) = \frac{1}{2\pi} \oint_\gamma \nabla\theta \cdot d\boldsymbol{\ell} \in \mathbb{Z}$$

---

### E12 â€” Finite-band dispersion rail

Band-limited growth rate:

$$\sigma(k) = r + a|k|^2 - b|k|^4, \quad \text{with } a, b > 0$$

---

### E13 â€” Band-pass amplitude evolution

Nonlinear band-pass evolution:

$$\partial_t A = \sigma(-i\nabla) A - \beta |A|^2 A$$

---

### E14 â€” Band-pass Lyapunov functional

Energy functional for band-pass dynamics:

$$\mathcal{E}[A] = \int \left( -r|A|^2 - a|\nabla A|^2 + b|\Delta A|^2 + \frac{\beta}{2}|A|^4 \right) dx$$

---

### E15 â€” Modal growth bound

Amplitude-square inequality per mode:

$$\frac{d}{dt} |\hat{A}_k|^2 \leq 2\sigma(k) |\hat{A}_k|^2 - c|\hat{A}_k|^4$$

---

### E16 â€” Randomness â†’ spectral concentration

Growth of initial broadband noise:

$$P_k(t) \propto P_k(0)\, e^{2\sigma(k)t}$$

$$\arg\max_k P_k(t) \to k^*$$

---

## C. Curvature Feedback & Lyapunov Dynamics

### E17 â€” Curvature operator

Nonlinear curvature-feedback operator:

$$\Theta[\psi] = -\frac{\nabla^2\psi}{\psi + \varepsilon\, e^{-\alpha|\psi|^2}}$$

---

### E18 â€” WCT Lyapunov functional

Curvature-plus-gradient energy:

$$\mathcal{E}[\psi] = \int \left( c_1 |\nabla\psi|^2 + c_2 |\Theta[\psi]|^2 \right) dx$$

---

### E19 â€” Spectral-gap â†” curvature invariant

Scaling relation between curvature and gap:

$$\Delta^* \sim \langle\sigma\rangle_w^2$$

---

### E20 â€” Higher-order cavity Lagrangian

Fourth-order cavity model (schematic):

$$\mathcal{L} = f(\psi) \left( \kappa S^2 + \theta P^2 - \gamma S P - \lambda \psi^2 \right)$$

---

### E21 â€” 4th-order cavity Eulerâ€“Lagrange (schematic)

Generalized EL for Lagrangians with second derivatives:

$$\frac{\delta\mathcal{L}}{\delta\psi} = \frac{\partial\mathcal{L}}{\partial\psi} - \partial_\mu \left( \frac{\partial\mathcal{L}}{\partial(\partial_\mu \psi)} \right) + \partial_\mu \partial_\nu \left( \frac{\partial\mathcal{L}}{\partial(\partial_\mu \partial_\nu \psi)} \right) = 0$$

---

### E22 â€” Effective metric

Matter-coupled metric deformation:

$$g_{\mu\nu}^{\text{eff}} = \eta_{\mu\nu} + \lambda \frac{\partial_\mu \psi\, \partial_\nu \psi}{\rho c^2} + \delta\eta_{\mu\nu} \frac{W_\psi}{W_0}$$

---

### E23 â€” Enthalpic curvature relation

Local enthalpy as energy plus curvature gradient:

$$h(\psi) \propto W_\psi + \chi |\nabla\psi|^2$$

---

## D. Dimensionality & Functional Bounds

### E24 â€” $n \leq 3$ stability bound

Embedding condition for pointwise control:

$$H^2(\mathbb{R}^n) \hookrightarrow L^\infty(\mathbb{R}^n) \Rightarrow n \leq 3$$

---

### E25 â€” Subcritical nonlinearity constraint

Nonlinearity exponent below critical Sobolev threshold:

$$p < p_c(n)$$

---

### E26 â€” Curvature norm bound

Curvature control via Sobolev norm:

$$\|\Theta[\psi]\|_{L^\infty} \leq C \|\psi\|_{H^2}$$

---

### E27 â€” Finite-energy confinement

WCT finite-energy condition:

$$\int_{\mathbb{R}^n} \left( |\nabla\psi|^2 + |\Theta[\psi]|^2 \right) dx < \infty$$

---

## E. Î±-Drop, Entropy Reduction, Pruning

### E28 â€” Î±-Drop exponent

Exponent defined from multiplicative pruning:

$$\alpha(n) = 1 + \frac{1}{n} \sum_{t=1}^{m(n)} \log_2 q_t(n) + \beta(n)$$

with $q_t(n) = \dfrac{M_t + 1}{M_t}$

---

### E29 â€” Entropy-drop pruning

State-count decay per step:

$$M_{t+1} \leq e^{-\Delta_t} M_t$$

---

### E30 â€” Spectral entropy

Entropy in Fourier space:

$$H_k(t) = -\sum_k P_k(t) \log P_k(t)$$

---

### E31 â€” Band-pass entropy drop

Curvature-induced entropy decrease (heuristic):

$$\Delta_t \gtrsim c_0 \left( k^{*2} \Delta_t \right)$$

---

### E32 â€” $\alpha < 1$ curvature-bounded search

Sub-exponential effective exploration:

$$\limsup_{n\to\infty} \alpha(n) < 1$$

---

### E33 â€” Support shrinkage

Support size controlled by entropy:

$$K_t \leq e^{H_k(t)}$$

---

### E34 â€” Energyâ€“entropy conversion

Curvature energy vs. entropy change:

$$\Delta E_t \geq \lambda\, \Delta H_k(t)$$

---

## F. WCC, Channel Capacity, P vs NP

### E35 â€” Curvature-locked fixed point

Locked WCT configuration:

$$W_\psi = -\frac{\nabla^2\psi}{\psi + \varepsilon\, e^{-\alpha|\psi|^2}}$$

$$\frac{d}{dt} S[\psi] \to 0$$

$$\nabla W_\psi \to 0$$

---

### E36 â€” Discrete WCC update

Local update rule with neighbourhood $N(x)$:

$$\psi^{(t+1)}(x) = U\left( \psi^{(t)}(x),\, \{\psi^{(t)}(y)\}_{y \in N(x)} \right)$$

---

### E37 â€” Bandlimit from energy

Maximal wavenumber from energy bound:

$$k_{\max} = C_1 \frac{E_{\max}}{\hbar c}$$

---

### E38 â€” Spatial channel capacity

Max mode count in volume $V$:

$$N_{\text{lanes}} \leq C_2\, V\, k_{\max}^3$$

---

### E39 â€” Time-step polynomial bound

Max update steps for input size $n$:

$$T_{\max}(n) \leq C_3\, n^d$$

---

### E40 â€” $P_{\text{WCC}} / NP_{\text{WCC}}$

Model-relative identification:

$$P_{\text{WCC}} = P$$

$$NP_{\text{WCC}} = NP$$

---

### E41 â€” Curvature-bounded configuration count

Configuration count under curvature rails:

$$|C_{\text{curv}}(n)| \leq 2^{\alpha(n)\, n}, \quad \text{with } \alpha(n) < 1$$

---

### E42 â€” Î˜-information identity

Coherence information decay:

$$\frac{d}{dt} I_{\text{coh}}[\psi] \propto -|\Theta[\psi]|^2$$

---

### E43 â€” Curvatureâ€“entropy tradeoff

Spectral entropy decay from curvature:

$$\frac{d}{dt} H_k(t) \leq -\mu\, |\Theta[\psi]|^2$$

---

## G. Resonant Cavity & Tokamak Scaling

### E44 â€” Î˜-eigenmode quantization

Curvature eigenmodes:

$$\Theta[\psi_n] = \lambda_n \psi_n$$

---

### E45 â€” Effective Q-factor

Quality factor with loss region $\gamma_{\text{loss}}$:

$$Q_{\text{eff}} = \omega \frac{\int u\, dV}{\int_{\gamma_{\text{loss}}} u\, dV}$$

---

### E46 â€” Plasmaâ€“cavity curvature match

Matched curvature averages:

$$\langle\sigma\rangle_{w,\text{plasma}} \approx \langle\sigma\rangle_{w,\text{cavity}}$$

---

### E47 â€” Power balance with curvature losses

Input vs loss and fusion:

$$P_{\text{in}} = P_{\text{loss}}(\psi) + P_{\text{fusion}}(\psi)$$

---

### E48 â€” Stability via curvature gap

Coreâ€“edge curvature gap criterion:

$$\Delta\sigma = \langle\sigma\rangle_{\text{core}} - \langle\sigma\rangle_{\text{edge}} > \Delta_{\text{crit}}$$

---

# Supplemental Wave Confinement Theory Equation Families (E49â€“E82)

*(Second-tier structural laws across Geometry of Resonance, Self-Emergent Cymatics, Enthalpic Aether, Randomness, Dimensionality, and P v. NP papers.)*

---

## H. Geometry-of-Resonance Extensions (Curvature, Phase) â€” E49â€“E56

### E49 â€” Curvature-modified Helmholtz effective mass

Gap-induced effective mass and spectrum:

$$m_{\text{eff}}^2 = \Delta^* c^2$$

$$\omega_j^2 = c^2 \lambda_j + \Delta^*$$

---

### E50 â€” Phase-coherence functional

Global phase coherence measure:

$$\mathcal{C}[\psi] = \int_\Omega |\nabla\theta|^{-1} |\psi|^2\, dx$$

---

### E51 â€” Curvatureâ€“gradient commutator

Non-commutativity of curvature and gradient (schematic):

$$[\Theta, \nabla]\psi = \nabla\left(\frac{\nabla^2\psi}{\psi + \cdots}\right) - \frac{\nabla^2(\nabla\psi)}{\psi + \cdots}$$

("â€¦" uses the same denominator structure as in $\Theta[\psi]$ from E17.)

---

### E52 â€” Nonlinear curvature gain/loss balance

Global curvature gain vs gradient loss:

$$G_\sigma = \int |\Theta|^2\, dx$$

$$L_\sigma = \int |\nabla\psi|^2\, dx$$


### E53 â€” Local curvature pressure-like density

Curvature penalty density (tied to the Lyapunov weight from E18):

$$p_\Theta(x) := c_2\, |\Theta[\psi](x)|^2$$

where $c_2$ is the curvature weight in the Lyapunov functional:

$$\mathcal{E}[\psi] = \int \left( c_1 |\nabla\psi|^2 + c_2 |\Theta[\psi]|^2 \right) dx$$

---

### E54 â€” Resonance-lock condition (stationary attractor)

Locked resonance state:

$$\partial_t \psi = 0$$

$$\delta\mathcal{E}[\psi] = 0$$

$$\nabla\Theta = 0$$

---

### E55 â€” Curvature-induced effective potential

Potential modified by curvature energy:

$$V_{\text{eff}}(\psi) = V(|\psi|^2) + \kappa\, |\Theta[\psi]|^2$$

---

### E56 â€” Phase-wall formation criterion

Phase-wall vs bulk curvature:

$$|\nabla\theta| \sim \sigma_{\text{wall}} \gg \langle\sigma\rangle_w$$

---

## I. Self-Emergent Fourier Cymatics (Swiftâ€“Hohenberg Structure) â€” E57â€“E64

### E57 â€” Swiftâ€“Hohenberg operator representation

Band-selective operator:

$$\mathcal{SH}[A] = (k^{*2} + \Delta)^2 A$$

---

### E58 â€” Band-selective Green's kernel

Spectral Green's function:

$$G(k) = \frac{1}{r + a(k^2 - k^{*2})^2}$$

---

### E59 â€” Projection onto dominant annulus

Let the dominant annulus be (discrete FFT spectrum):

$$
\mathcal{A}^{\star}
:= \{\, k \in Z^{d} : \lvert k \rvert - k_{\star} \le \Delta k \,\}
$$



Then the band-projection of $A$ is:

$$
(P_{k_{\star}} A)(x)
:= \sum_{k \in \mathcal{A}^{\star}} \hat{A}_{k}\, e^{i\,k\cdot x}
$$



---


### E60 â€” Center-manifold amplitude equation

Reduced amplitude dynamics:

$$\partial_T \mathcal{A} = \mu \mathcal{A} - g|\mathcal{A}|^2 \mathcal{A}$$

---

### E61 â€” Pattern formation threshold

Critical growth parameter:

$$r_c = \min_k \left[ a(k^2 - k^{*2})^2 \right] = 0$$

---

### E62 â€” Spectral energy concentration

Energy fraction in dominant modes:

$$\eta(t) = \frac{\sum_{k \in \mathcal{A}^*} |\hat{A}_k|^2}{\sum_k |\hat{A}_k|^2}$$

---

### E63 â€” Entropic mode selection

Entropy-weighted mode preference:

$$k^* = \arg\min_k \left[ H_k + \lambda\, C_\Theta(k) \right]$$

---

### E64 â€” Pattern wavelength from curvature

Characteristic scale from curvature balance:

$$\lambda^* = \frac{2\pi}{k^*} = 2\pi \sqrt{\frac{b}{a}}$$

---

## J. Dimensionality Bounds & Sobolev Structure â€” E65â€“E70

### E65 â€” Critical Sobolev exponent

Dimension-dependent critical power:

$$p_c(n) = \frac{n + 2}{n - 2} \quad (n > 2)$$

---

### E66 â€” Gagliardoâ€“Nirenberg interpolation

Interpolation inequality:

$$\|u\|_{L^p} \leq C \|\nabla u\|_{L^2}^\theta \|u\|_{L^2}^{1-\theta}$$

---

### E67 â€” Embedding failure for $n > 3$

Counterexample existence:

$$\exists\, \psi \in H^2(\mathbb{R}^n) : \psi \notin L^\infty(\mathbb{R}^n) \quad \text{if } n > 3$$

---

### E68 â€” Energy concentration bound

Localized energy control:

$$\int_{B_R} |\nabla\psi|^2\, dx \leq C R^{n-2} \|\psi\|_{H^1}^2$$

---

### E69 â€” Curvature regularity requirement

Minimum regularity for bounded curvature:

$$\psi \in H^2 \Rightarrow \Theta[\psi] \in L^\infty \quad \text{iff } n \leq 3$$

---

### E70 â€” Dimensional stability criterion

Combined bound:

$$n \leq 3 \iff H^2 \hookrightarrow L^\infty \text{ and } p < p_c(n)$$

---

## K. P vs NP Computational Bounds â€” E71â€“E76

### E71 â€” Physical computation bound

Spacetime resource limit:

$$T \cdot V \cdot k_{\max}^3 \leq C_{\text{phys}}$$

---

### E72 â€” Curvature-pruned search space

Effective configuration count:

$$|S_{\text{eff}}(n)| \leq 2^{\alpha(n) n}$$

---

### E73 â€” Polynomial verification

Verifier constraint:

$$V(x, w) \in P \quad \text{for } |w| = \text{poly}(|x|)$$

---

### E74 â€” Curvature separation conjecture

Gap between classes:

$$\inf_n \left[ \frac{\log |NP_n|}{\log |P_n|} \right] > 1$$

---

### E75 â€” Physical oracle impossibility

No polynomial-time curvature oracle:

$$\nexists\, O : O(\psi) = \arg\min_\psi \mathcal{E}[\psi] \text{ in poly time}$$

---

### E76 â€” WCC complexity equivalence

Model-theoretic identification:

$$P_{\text{WCC}} = P \implies \text{WCC captures physical computation}$$

---

## L. Entropy & Information Dynamics â€” E77â€“E82

### E77 â€” Mutual information decay

Information loss rate:

$$\frac{d}{dt} I(\psi; \psi_0) \leq -\gamma\, \mathcal{E}_\Theta[\psi]$$

---

### E78 â€” Fisher information bound

Curvatureâ€“Fisher relation:

$$\mathcal{I}_F[\psi] \geq c\, \int |\Theta[\psi]|^2\, dx$$

---

### E79 â€” Entropy production rate

Irreversibility measure:

$$\dot{\Sigma} = \frac{d H_k}{dt} + \frac{\mathcal{E}_\Theta}{T_{\text{eff}}}$$

---

### E80 â€” Landauer bound analog

Minimum energy per entropy reduction:

$$\Delta E \geq k_B T_{\text{eff}} \ln 2 \cdot \Delta H$$

---

### E81 â€” Coherence length from entropy

Characteristic scale:

$$\xi_{\text{coh}} = \left( \frac{\mathcal{E}[\psi]}{H_k} \right)^{1/2}$$

---

### E82 â€” Informationâ€“geometry duality

Curvature as information metric:

$$g_{ij}^{(\text{info})} = \langle \partial_i \Theta\, \partial_j \Theta \rangle$$

---

# Curvature-Locking Equations (CLE1â€“CLE10)

## CLE1 â€” Curvature-Locking Functional (Toroidal Form)

$$S[\psi] = \int_\mathcal{M} \left[ |\nabla\psi|^2 + |W_\psi - \sigma_\star|^2 \right] \sqrt{g}\, d^3x$$

$$W_\psi := -\frac{\nabla^2\psi}{\psi}$$

---

## CLE2 â€” Eulerâ€“Lagrange (Curvature-Lock)

$$-\nabla^2\psi + (W_\psi - \sigma_\star) \cdot \frac{\nabla^2\psi}{\psi^2} = 0$$

---

## CLE3 â€” Curvature-Locking Condition

$$W_\psi = \sigma_\star \quad \text{(spatially uniform curvature)}$$

---

## CLE4 â€” Effective Equation for Locked Ïˆ

$$-\nabla^2\psi = \sigma_\star \cdot \psi$$

---

## CLE5 â€” Laplacian on Torus (Flat Embedding)

$$\nabla^2\psi = \frac{1}{R^2} \partial_\theta^2 \psi + \frac{1}{r^2} \partial_\phi^2 \psi$$

---

## CLE6 â€” Separation Ansatz

$$\psi(\theta, \phi) = f(\theta)\, g(\phi)$$

Yields:

$$\frac{f''(\theta)}{f(\theta)} + \frac{R^2}{r^2} \cdot \frac{g''(\phi)}{g(\phi)} = -\sigma_\star R^2$$

---

## CLE7 â€” Reduced Angular ODE (Thin-Torus Limit)

$$f''(\theta) + \sigma_\star^2 f(\theta) = 0$$

Only smooth $2\pi$-periodic solution under curvature locking is constant $f$.

---

## CLE8 â€” Ïˆ-Electron Eigenmode Solution

$$\psi(\theta, \phi) = A\, e^{i\phi}$$

Unique curvature-locked toroidal eigenmode.

---

## CLE9 â€” Electron Radius from Curvature

$$R = \frac{1}{\sigma_\star}$$

For the electron: $R \approx 386.3$ fm.

---

## CLE10 â€” Curvature Scalar Identity

$$W_\psi = -\frac{\nabla^2\psi}{\psi} = \sigma_\star^2$$

Ties together curvature scalar, eigenmode equation, and feedback-collapsed Ïˆ-electron solution.

---

## G1 â€” Ghost-mode modulation (JUNO phenomenology)

$$\delta_g(E) = A_g \cos\left( k_\ell \ln\frac{E}{E_0} + \phi \right)$$

---

# ðŸŒŒ Wave Confinement Theory (WCT) â€” Cosmology Equation Set (CM1â€“CM20)

> **Module:** `WCT Cosmology Core`  
> **Scope:** CMB Spectrum, Primordial Evolution, Sound Horizon Physics  
> **Reference:** Addendum to `EQUATIONS.md`, citing `Geometry of Resonance` and `WCT Cosmology Notebook v2`

---

## ðŸ“˜ Overview

This document defines the **complete minimal equation set** (CM1â€“CM18) for cosmological modeling using Wave Confinement Theory (WCT) instead of General Relativity (GR). These equations:

- Replace inflation and Friedmann dynamics
- Generate CMB acoustic peaks from curvature principles
- Are partially implemented in your current WCT simulator

---

## CM1 â€” Fundamental Field Evolution

$$i\, \partial_t \psi = -\Theta[\psi] \cdot J[\psi]$$

$$\Theta[\psi] = -\frac{\Delta\psi}{\psi + \varepsilon \cdot e^{-\alpha|\psi|^2}}$$

$$J[\psi] = |\psi|^2 \cdot \nabla^2\psi \cdot \varepsilon_{\text{vac}}$$

---

## CM2 â€” Curvature-Spectral Tilt

$$P_{\text{prim}}(k) \sim k^{-\alpha_{\text{WCT}}}$$

$$n_s - 1 = -\alpha_{\text{WCT}}$$

$$\alpha_{\text{WCT}} = -\frac{d(\ln|\Theta(k)|)}{d(\ln k)}$$

---

## CM3 â€” Gravitational Potential from Î˜

$$\Phi(k, t) = -C_\Phi \cdot \frac{\Theta(k, t)}{k^2}$$

---

## CM4 â€” Horizon-Entry Potential Decay

$$\partial_t \Phi(k, t) = -\Gamma(k, t) \cdot \Phi(k, t)$$

$$\Gamma(k, t) = \left| \frac{\partial_t \Theta(k, t)}{\Theta(k, t)} \right|$$

---

## CM5 â€” WCT Analog Oscillators

$$\ddot{\delta}_\gamma + c_s^2(t) \cdot k^2 \cdot \delta_\gamma = -k^2 \cdot \Phi$$

$$\ddot{\delta}_b + \mathcal{R}(t) \cdot c_s^2(t) \cdot k^2 \cdot \delta_\gamma = -k^2 \cdot \Phi$$

$$\mathcal{R}(t) = \frac{E_{\text{comp}}}{E_{\text{rad}}}$$

---

## CM6 â€” Sound Speed from Curvature Feedback

$$c_s^2(t) = \frac{1}{3(1 + \mathcal{R}(t))} \left[ 1 - \beta_{\text{curv}} \cdot \frac{E_{\text{curv}}(t)}{E_{\text{tot}}} \right]$$

---

## CM7 â€” Curvature Diffusion (Silk Analog)

$$\partial_t \delta_\gamma \to \partial_t \delta_\gamma - D_{\text{curv}}(t) \cdot k^2 \cdot \delta_\gamma$$

$$D_{\text{curv}}(t) = \frac{\langle|\nabla\psi|^2\rangle}{\langle|\psi|^2\rangle}$$

---

## CM8 â€” Initial Conditions (Sachsâ€“Wolfe Form)

$$\delta_\gamma(0) = \delta_b(0) = -2 \cdot \Phi(k, 0)$$

$$\Phi(k, 0) = 2 \cdot C_\Phi \cdot \frac{\Theta(k, 0)}{k^2}$$

---

## CM9 â€” First-Order Mode Evolution

$$\dot{\delta}_\gamma = v_\gamma$$

$$\dot{v}_\gamma = -c_s^2 \cdot k^2 \cdot \delta_\gamma - k^2 \cdot \Phi$$

$$\dot{\delta}_b = v_b$$

$$\dot{v}_b = -\mathcal{R}(t) \cdot c_s^2 \cdot k^2 \cdot \delta_\gamma - k^2 \cdot \Phi$$

---

## CM10 â€” Tight Coupling Drag

$$\delta_b \leftarrow (1 - \varepsilon_{\text{drag}}) \cdot \delta_b + \varepsilon_{\text{drag}} \cdot \delta_\gamma$$

$$\varepsilon_{\text{drag}}(t) = \frac{E_{\text{exch}}}{E_{\text{comp}}}$$

---

## CM11 â€” Curvature Damping Envelope

$$D(k) = \exp\left( -\frac{k^2}{k_D^2} \right)$$

$$k_D^{-2} = \int_0^{t^*} D_{\text{curv}}(t)\, dt$$

---

## CM12 â€” Dimensionless Power Spectrum

$$\Delta^2(k) = \frac{k^3}{2\pi^2} \cdot P(k)$$

---

## CM13 â€” Peak Metrics

$$r_{21} = \frac{P(k_2)}{P(k_1)}, \quad r_{31} = \frac{P(k_3)}{P(k_1)}$$

$$s_{21} = \frac{k_2}{k_1}, \quad s_{31} = \frac{k_3}{k_1}$$

---

## CM14 â€” Peak Interpretation

- Fast Î˜ decay â†’ $s_{ij}$ â†‘
- High compression â†’ $r_{31}$ â†‘
- High radiative energy â†’ $r_{21}$ â†“

---

## CM15 â€” Angular Scaling from $a_{\text{WCT}}$

$$k \to \frac{k}{a_{\text{WCT}}(t)}$$

$$a_{\text{WCT}}(t) = \left[ \frac{E_{\text{curv}}(0)}{E_{\text{curv}}(t)} \right]^{1/3}$$

---

## CM16 â€” Horizon Scale (WCT Form)

$$R_{\text{hor}}(t) = \int_0^t c_s(t')\, dt'$$

$$k_{\text{hor}} = \frac{2\pi}{R_{\text{hor}}}$$

---

## CM17 â€” Curvature Energy Conservation

$$E_{\text{curv}}(t) + E_{\text{grad}}(t) = E_{\text{tot}}$$

---

## CM18 â€” Closure Law (WCT Minimal Set)

$$\{ \text{CM1} + \text{CM2} + \text{CM3} + \text{CM4} + \text{CM5} + \text{CM7} \}$$

---

## CM19 â€” Acoustic Horizon from Î˜

$$c_s(t) = \sqrt{ \frac{\partial P_{\text{curv}}}{\partial \rho_{\text{curv}}} }$$

---

## CM20 â€” Î˜-Based Expansion Law

$$H(t) = \frac{\dot{a}_{\text{WCT}}}{a_{\text{WCT}}} = \sqrt{ \frac{\rho_\Theta(t)}{3|K|} }$$

---

# Correction Notes and Canonical Alignment

This section records notation, closure, and consistency corrections applied to the preceding analysis. No new physical assumptions are introduced. All changes align the presentation with the canonical Wave Confinement Theory (WCT) equation set (E17â€“E18, E30, E34, E43).

---

### 1. Lyapunov Energy Functional

Earlier drafts referenced the curvature penalty

$$E_\Theta = \int |\Theta[\psi]|^2\,dx$$

as a stability proxy. This has been corrected to the full WCT Lyapunov candidate

$$\mathcal{E}_{\text{WCT}}[\psi] = \int \left( |\nabla\psi|^2 + |\Theta[\psi]|^2 \right) dx,$$

consistent with the canonical formulation (E18). The quantity $E_\Theta$ is retained only as the curvature component within $\mathcal{E}_{\text{WCT}}$.

---

### 2. Spectral Curvature Closure

In the spectral analysis, the denominator of $\Theta[\psi]$ was approximated by a constant amplitude scale. This approximation is now made explicit via the effective closure

$$D_{\text{eff}}^2 := \langle |\psi|^2 \rangle + \varepsilon^2,$$

leading to the curvature cost

$$C_\Theta(k) = \frac{k^4}{D_{\text{eff}}^2}.$$

This clarifies that the $k^4$ spectral penalty arises from a meanâ€“amplitude (weakâ€“intermittency) closure rather than an exact identity.

---

### 3. Symbol Disambiguation in the Spectral Functional

To avoid collision with the nonlinear saturation parameter $\alpha$ appearing in the definition of $\Theta[\psi]$, the spectral free-energy weights have been relabeled:

$$\alpha \to \lambda_\Theta, \qquad \beta \to \lambda_{\text{ex}}.$$

No change in functional form or interpretation is implied.

---

### 4. Macroâ€“Micro Control Parameter

The regime parameter governing entropy-dominated versus curvature-dominated behavior is redefined in observable terms as

$$\Xi = \frac{\int k^4 \rho(k)\, dk}{H}, \qquad H = -\sum_k P_k \log P_k,$$

eliminating reliance on an undefined "noise temperature" and aligning the definition with the spectral entropy (E30).

---

### 5. Entropyâ€“Curvature Relation

The empirical entropyâ€“curvature coupling is stated in its canonically bounded form

$$\frac{dH}{dt} \leq -\mu\, |\Theta[\psi]|^2,$$

consistent with the curvatureâ€“entropy tradeoff (E43) and its integrated variant (E34).

---

### 6. Isoelectronic Flow Consistency

The imaginary-time isoelectronic evolution equation is explicitly identified as a radially reduced, imaginary-time sector of the unified curvatureâ€“wavefield equation (UWCT), with ultraviolet smoothing and norm enforcement included for numerical well-posedness. No additional dynamical primitives are introduced.

---

### 7. Scope of Corrections

All corrections in this section are:

- notational or definitional clarifications,
- explicit statements of previously implicit closures,
- alignments with the canonical WCT master equations.

They do not alter the qualitative or quantitative conclusions of the empirical results, but ensure internal consistency, symbol hygiene, and direct traceability to the WCT core equation architecture.

---

# End of WCT Equations Master Document
