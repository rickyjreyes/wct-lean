# Phase VIII proof and formalization ledger

The Phase VII conventional proof has been rechecked against the exact
functional on X=H²(R²;C), M=integral |u|² and
H=||(Delta+1)u||²-beta||u||_4^4/2+beta||u||_6^6/3. The dyadic beta and
m_D4 are unchanged. No mathematical error was found. The result is full
ambient-space stability of the entire minimizing set, including nonsymmetric
and mass-changing perturbations; no D4 restriction is imposed on X.

| Proposition | Verified mathematical input | Conclusion/status |
|---|---|---|
| Boundedness and continuity | Pointwise completed square; D<=2T+2M; H² algebra | PROVED: coercivity and smooth energy; I finite and locally Lipschitz, continuous at 0 |
| Strict energy-per-mass decrease | Exact dilation adjustment, D<=rho M, Fourier constant 1/4, negative anisotropic Gaussian trial | PROVED for 0<a<b, a+b<2B0 |
| Frozen threshold | Exact dyadic inequality 9-rho m²>0 | PROVED and kernel checked; B0=3/sqrt(rho) is sufficient, not asserted sharp |
| All-split quantitative binding | Upper-half Gaussian trial floor; exact slack; smaller/larger split assembly | PROVED conventionally for all 0<mu<m; no finite scan |
| Attainment/compactness | Nonvanishing, translated weak H² extraction, Hilbert and Brezis-Lieb splitting, binding, strong remainder convergence | PROVED for every mass-m minimizing sequence modulo translations |
| Exact stationary states | Lagrange multiplier, H² algebra and elliptic bootstrap | PROVED: smooth global constrained minimizers; no identification with FEM or symmetry/uniqueness theorem |
| Global flow | H²-algebra Duhamel contraction, smooth approximation, conservation, coercivity | PROVED for arbitrary complex H² data in R² |
| Orbital stability | Conservation plus near-mass normalization and minimizing-sequence compactness | PROVED for the entire minimizing set, not each individual orbit |
| Confinement observable | Uniform tightness modulo translations and L² control | PROVED: for every alpha some finite R and positive basin give infinite exit time; no numeric R/basin claimed |

## Independent checks of the vulnerable steps

The Gaussian uses exp(ix), not an assumed real or D4 profile. The admissible
class is full complex H², so this is legal. Every mass has a negative trial.
The dilation polynomial is minimized algebraically; no differentiability of
an H²-valued dilation orbit or existence of a minimizer is assumed. The
Fourier Cauchy-Schwarz integral has constant 1/(8 sqrt(eta)) under the stated
unitary two-dimensional convention; optimizing yields ||u||_infinity²<=sqrt(MD)/4.
This integral diverges in dimension four and is not exported there.

The sextic sign is handled by the adjusted-sequence cap; unrestricted
amplitude scaling alone would not suffice. For s=min(mu,m-mu), b=m-s,
the Gaussian bound is needed only for b in [m/2,m]. The per-mass order
also handles s=b, so no midpoint exception remains. The exact gap is

    I(mu)+I(m-mu)-I(m) >= kappa s > s/3000000,
    kappa=(221/100000)*(7 beta m/1760-1/50)^2 /
                    [4*(30203/40000+beta m²/8100)].

Continuity makes the gap tend to zero at both endpoints; a uniform positive
absolute gap is neither claimed nor required. In the compactness proof,
strong L² plus the uniform H²-to-L-infinity bound kills both nonlinear
remainder norms. Energy splitting then forces the A remainder norm to zero,
which with L² gives strong H². This also rules out residual high-frequency
energy at zero residual mass. Translation is the only noncompact symmetry
used; phases are included in the minimizing set. In the stability argument,
nearby masses are normalized by factors tending to one on uniformly bounded
H² sets, so both energy and distance errors vanish.

## Six new kernel-checked theorems (45 D4 total)

The source is `WCTLean/Models/D4Closure.lean`, imported by the maintained
library root. It preserves the old 28+11 theorems byte-for-byte.

1. `gaussian_energy_floor_pos`: exact frozen Gaussian energy-floor positivity.
2. `gap_constant_factorization`: exact factorization of the rational gap.
3. `frozen_per_mass_nonincreasing`: order on the full mass interval from the
   explicit adjusted-sequence inputs, including equal component masses.
4. `frozen_quantitative_all_splits`: the exact requested strict all-mu
   inequality, with visible sequence and upper-half Gaussian premises.
5. `frozen_I2_quantitative_all_splits`: specialization to the actual declared
   integral-infimum syntax, with the same visible analytic premises.
6. `frozen_no_energy_dichotomy`: excludes energy splitting from those inputs.

The main theorem type is, in mathematical notation:

    BindingSequenceInputs I beta beta B0 ->
    (forall b in [m/2,m], I(b)<=-b gaussianEnergyFloor) ->
    forall mu in (0,m), min(mu,m-mu)/3000000 < I(mu)+I(m-mu)-I(m).

No binding or attainment hypothesis is inserted in place of its derivation.
The proof derives the needed order, supplies the exact slack, controls the
Gaussian floor and assembles the symmetric split. The `I2` wrapper retains
the explicit `WholeSpaceData` input: it is not yet a concrete Sobolev space.

At commit ae3b4c37065f9648f5d1bd894e3c5c0802fd9f41, both formal and
container workflows passed, 7,259 build jobs. The three principal new
conclusions have only propext, Classical.choice and Quot.sound in their
kernel dependency lists. No sorry, admit, custom axiom or unsafe proof
oracle was added. This is meaningful additional formal assembly, not full
formal closure of the continuum model.

## Exact remaining formal bridges

1. Instantiate `WholeSpaceData.H2` and `weakLaplacian` with the actual complex
   Sobolev space; prove integrability and the meanings of all declared integrals.
2. Prove the Fourier constant, change-of-variables identities, negative
   Gaussian integrals, and the existence of dilation-adjusted minimizing
   sequences/trials for the concrete infimum. These discharge
   `BindingSequenceInputs` and the upper-half Gaussian premise above.
3. Formalize local nonvanishing/extraction, Brezis-Lieb for p=4,6 and the
   strong H² remainder argument. Binding then excludes the extracted split;
   the kernel theorem alone does not construct a concentration decomposition.
4. Instantiate `VariationalCompactnessInputs`; existing kernel theorems then
   give attainment. No additional unproved existence assumption is needed.
5. Formalize the actual global flow, continuity and conservation, and derive
   near-mass energy trapping from concrete compactness. Instantiate the
   existing nearby-mass stability theorem using distance to the full set.

These are missing formalizations of established conventional mathematics,
not reasons to reopen its conventional conclusions. The new four-dimensional
curvature counterexample and the periodic spectral certificate are separate
conventional/computer-assisted results; neither is falsely listed as Lean checked.
