# D4 Phase VII: independent analytical audit and confinement theorem

Execution date: 2026-10-25. The model is **two dimensional**. D4 labels a
square-symmetric numerical branch, not four spatial dimensions. The unrestricted
variational class below does not impose that symmetry. This audit independently
reconstructs the written theorem in geometry_of_resonance PR36, head
`31f322c94d2ef32b20acea741884514806025c85`; it does not claim that theorem is new.
The uniform rational split gap and explicit confinement-observable consequence
below extend the verification record. Mathematical proof and Lean instantiation
are separate: the continuum arguments here are not yet kernel checked.

## 1. Exact object and elementary estimates

Let X=H²(R²;C), A=Δ+1, M(u)=∫|u|², D=∥Δu∥²₂, K=∥∇u∥²₂,
T=∥Au∥²₂, Q=∥u∥⁴₄, S=∥u∥⁶₆. Then

    H=T−βQ/2+βS/3,   I(m)=inf{H(u):M(u)=m},   I(0)=0,
    β=4608178181141995/1125899906842624,
    m₀=1432536998431173/562949953421312.

All norms are integral norms. T has coefficient one. There is no torus,
band restriction, real-valued restriction or projection in this definition.
The evolution is i u_t=A²u−β|u|²u+β|u|⁴u.

For r≥0, −βr²/2+βr³/3=(β/3)r(r−3/4)²−3βr/16.
Consequently H≥T−cM with c=3β/16. Also D≤2T+2M and K≤√(MD).
Fixed mass and bounded energy from above therefore bound the full H² norm.
H²(R²) embeds in L∞ and is a Banach algebra; M,H are real smooth functions
on X, uniformly Lipschitz on bounded sets. In particular I is finite below.

Here is an explicit negative trial at **every** m>0. Set
f_ab=(πab)^(-1/2)exp[−x²/(2a²)−y²/(2b²)] and
u_R=√m R^(-1) f_ab(x/R,y/R) exp(ix). Direct Gaussian integration gives

    M(u_R)=m,
    H(u_R)=c₂/R²+c₄/R⁴,
    c₂=2m/a²−βm²/(4πab),
    c₄=m[3/(4a⁴)+1/(2a²b²)+3/(4b⁴)]+βm³/(9π²a²b²)>0.

Choose a/b>8π/(βm). Then c₂<0 and R²=−2c₄/c₂ gives
I(m)≤−c₂²/(4c₄)<0. Hence −cm≤I(m)<0, and I is continuous at zero.
On a compact positive mass interval, near-minimizers with H≤1 have uniform
H² bounds by coercivity. Amplitude normalization from mass a to b changes
H by O(|a−b|), uniformly there, since the energy is a cubic polynomial in
the squared amplitude. Applying this in both directions proves that I is
locally Lipschitz on (0,∞).

## 2. Every scaling term and the decisive improved estimate

For u_λ(x)=λu(λx), M is unchanged, D and S multiply by λ⁴, K and Q by λ²:

    H(u_λ)=(D+βS/3)λ⁴−(2K+βQ/2)λ²+M.

For √t u, M,T multiply by t, Q by t² and S by t³. Therefore

    H(√t u)/t = T−βtQ/2+βt²S/3.

The positive sextic term prevents a universal decreasing-amplitude-energy
claim. For example narrow large-amplitude profiles violate that shortcut.
Instead adjust an arbitrary mass-a minimizing sequence by **minimizing the
exact dilation polynomial**. Its coefficients P=D+βS/3 and B=2K+βQ/2 are
strictly positive for a nonzero H² field. The minimum is at λ²=B/(2P), with
exact defect P(λ²−B/(2P))². The adjusted sequence w_n is still minimizing,
since I(a)≤H(w_n)≤H(u_n), and satisfies

    D−K−βQ/4+βS/3=0.                         (V)

No minimizer, convergence of the dilation factors, or differentiability of
the spatial orbit as an H²-valued curve is used. Combining (V) with
T=D−2K+M and completing a square gives the exact identity

    D+T+(2β/3)∫r(r−3/8)² = ρM,
    ρ=1+3β/32=49853331562389953/36028797018963968.

Thus D≤ρM for every adjusted profile. Independently, using the unitary
two-dimensional Fourier convention û=(2π)^(-1)∫exp(−ix·ξ)u(x)dx,
Cauchy–Schwarz gives, for η>0,

    ∥u∥²∞ ≤ (D+ηM)/(8√η),
    (2π)^(-2)∫R² (|ξ|⁴+η)^(-1)dξ = 1/(8√η).

The integral follows in polar coordinates by s=r² and an elementary
arctangent integral. Density, or directly the L¹ Fourier bound, extends the
inequality from Schwartz functions to H². For M>0 also D>0: a zero
Laplacian norm forces an L² Fourier transform supported at a single point,
hence the zero field. Choosing η=D/M proves

    ∥u∥²∞≤√(MD)/4,   S(w_n)≤(√ρ/4)a Q(w_n).  (R)

This estimate is specific to dimension two; the analogous integral diverges
logarithmically in dimension four. It cannot be exported to H²(R⁴).

## 3. Strict binding at the frozen mass, including both endpoints

Put B₀=3/√ρ. For 0<a<b with a+b<2B₀, set t=b/a and
h=1−(a+b)/(2B₀)>0. Applying (R) to the adjusted sequence gives

    I(b)/t ≤ H(√t w_n)/t
      ≤ H(w_n)−(t−1)(β/2)h Q(w_n)
      ≤ [1+(t−1)h]H(w_n),

where the last step uses H≥−βQ/2. Passing to the limit preserves a
**sequence-independent** strict defect:

    I(a)/a−I(b)/b ≥ (b−a)(−I(a))h/a² >0.     (E)

Exact rational arithmetic proves 9−ρm₀² equals

    454708712324087584212476662678391978900775591 /
    11417981541647679048466287755595961091061972992 >0.

Thus m₀<B₀. For every 0<μ<m₀, both I(μ)/μ and
I(m₀−μ)/(m₀−μ) strictly exceed I(m₀)/m₀ by (E). Multiplying by the
positive component masses and adding proves, unconditionally for the
specified continuum functional,

    I(m₀)<I(μ)+I(m₀−μ) for ALL 0<μ<m₀.        (BIND)

The same proof works for 0<m≤B₀. B₀ is a **sufficient binding threshold**,
not a proved sharp transition or a universal physical critical mass.

### New uniform rational lower bound

Let s=min(μ,m₀−μ), b=m₀−s∈[m₀/2,m₀]. The Gaussian above with a=10,
transverse width 1 has

    c₂(b)=b/50−βb²/(40π),
    c₄(b)=b[30203/40000+βb²/(900π²)],
    I(b)≤U(b)=−c₂(b)²/(4c₄(b)).

Define the EXACT RATIONAL numbers

    h*=221/100000,
    d*=7βm₀/1760−1/50,
    C*=30203/40000+βm₀²/8100,
    κ=h* d*²/(4C*).

The independent rational verifier and Lean additions prove d*,C*,κ>0
and h*≤1−m₀/B₀. Using 3<π<22/7, we have −c₂(b)≥bd* and c₄(b)≤bC*,
so −I(b)≥−U(b)≥bd*²/(4C*). Since e(s)≥e(b), including equality s=b,
(E) applied to b<m₀ yields

    Δ(μ):=I(μ)+I(m₀−μ)−I(m₀)
      ≥m₀[e(b)−e(m₀)]
      ≥m₀ s h* [−I(b)]/b²
      ≥ κ min(μ,m₀−μ)>0.                    (GAP)

This is a continuous, all-split rational lower bound, with no numerical
partition or uncovered endpoint interval. It tends to zero at either
endpoint, as it must: continuity gives Δ→0. There is no uniform positive
gap on the open split interval. Interior equality is excluded. General
subadditivity also follows independently by separated compact smooth
near-minimizers, but does not supply strictness by itself.

## 4. Attainment: the actual loss mechanisms

Take any mass-m₀ minimizing sequence. Coercivity bounds it in H². If its
supremum unit-ball L² mass vanishes, a bounded-overlap cube cover and the
local H¹ interpolation inequality imply Q→0. The uniform L∞ bound then
gives S→0, contradicting I(m₀)<0 and T≥0. Thus translations and a subsequence
give a nonzero weak H² limit u, strong local Lp convergence for every finite
p, and almost-everywhere convergence. Let a=M(u), 0<a≤m₀, and v_n=u_n−u
in the translated coordinates.

Weak Hilbert splitting gives M(v_n)=m₀−a+o(1) and
T(u_n)=T(u)+T(v_n)+o(1). Brezis–Lieb at p=4 and p=6, separately, gives
H(u_n)=H(u)+H(v_n)+o(1). Its hypotheses hold for complex fields: a.e.
convergence and boundedness in those Lp spaces. The opposite nonlinear
signs do not obstruct either identity. If a<m₀, normalizing v_n to mass
m₀−a changes H by o(1), and hence

    I(m₀)≥H(u)+I(m₀−a)≥I(a)+I(m₀−a),

contradicting (BIND). This excludes dichotomy and every diffuse
positive-mass remainder. Thus a=m₀. Now v_n→0 in L²; bounded L∞ norms
give Q(v_n),S(v_n)→0. Energy splitting, H(u)≥I(m₀), and T(v_n)≥0 force
H(u)=I(m₀) and T(v_n)→0. Then
∥Δv_n∥₂≤∥Av_n∥₂+∥v_n∥₂→0, and interpolation gives strong H² convergence.
In particular zero-mass high-frequency remnants cannot retain energy.

Therefore G={M=m₀,H=I(m₀)} is nonempty and every minimizing sequence is
precompact modulo translations. Phase drift is harmless because U(1) is
compact and G includes all phases. The proof does not assert any D4
symmetry, uniqueness, reality or identity with the computed periodic root.

Brezis–Lieb is an external established theorem, not an unproved model
hypothesis: H. Brezis and E. Lieb, Proc. AMS 88 (1983), 486–490,
https://sites.math.rutgers.edu/~brezis/PUBlications/99-journal.pdf .
The extraction/vanishing framework is Lions, AIHPC 1 (1984), 109–145,
https://www.numdam.org/article/AIHPC_1984__1_2_109_0.pdf . The above verifies
the model-specific steps rather than importing a pure-power existence theorem.

## 5. Exact states, global flow and orbital stability

Each Q∈G is an exact constrained global minimizer and thus a constrained
critical point. The real Lagrange multiplier rule gives
A²Q−β|Q|²Q+β|Q|⁴Q=ωQ in H^(-2). The multiplier of A²+1 is elliptic of
order four; the H² algebra property and iteration give Q∈H^s for every
finite s. Uniform continuity and L² imply Q(x)→0 at infinity. The scalar
dilation minimum also applies to Q, and (R) and the equation imply

    ωm₀=I(m₀)−βQ₄/2+2βS₆/3
      ≤I(m₀)−(β/2)(1−m₀/B₀)Q₄<I(m₀)<0.

Here Q₄,S₆ are integrals, not the profile symbol. The standing wave is
exp(−iωt)Q with this convention. Using exp(+iωt) requires reversing the
frequency sign in the stationary equation and linearization.

The group exp(−itA²) is unitary on H². The polynomial nonlinearity is locally
Lipschitz H²→H², so Duhamel contraction gives a unique local mild solution,
continuous dependence and an H² blow-up alternative. Smooth approximation
and local continuous dependence pass the smooth mass and Hamiltonian
conservation laws to H² solutions. Smooth persistence follows by tame
product estimates while the H² norm is bounded. Conservation and
T≤H(u₀)+cM(u₀), D≤2T+2M exclude the blow-up alternative in both directions.
This establishes the global flow for arbitrary complex H² data.

For every ε>0 there exists δ>0 such that

    dist_H²(u₀,G)<δ ⇒ sup_(t∈R) dist_H²(u(t),G)<ε.       (ORB)

Proof: otherwise take initial data approaching G and exit times t_n.
G is uniformly H² bounded, so initial masses approach m₀ and energies
approach I(m₀); conservation preserves these limits. Coercivity bounds the
evolved fields. Normalize their masses to m₀ by factors tending to one;
this changes both H² distance and H by o(1). They are minimizing, so the
compactness just proved contradicts the fixed positive exit distance.
This includes mass-changing perturbations. It concerns the **whole set G**,
not each separate phase/translation orbit, attraction, or the periodic root.

## 6. New confinement observable and lifetime consequence

For nonzero u define C_R(u)=sup_y ∫_(B(y,R))|u|²/M(u). This observable
allows translation; a fixed laboratory ball would measure transport as loss.
For 0<α<1 set T_exit=inf{t≥0:C_R(u(t))<1−α}, with inf ∅=∞.

For every α there are finite R and δ>0 such that

    dist_H²(u₀,G)<δ ⇒ C_R(u(t))≥1−α for all t∈R,
    hence T_exit=∞.                                    (CONF)

Proof: compactness of G modulo translations implies uniform tightness.
Otherwise a sequence Q_n∈G with no ball of radius n retaining 1−α/4 of
its mass would contradict a translated strongly L² convergent subsequence.
Choose R accordingly. For v close in L² to Q∈G, the integral over any
measurable set changes by at most (∥v∥₂+√m₀)∥v−Q∥₂, and the same bound
controls its total mass. Choosing a sufficiently small distance makes the
ratio at least 1−α. Apply (ORB), allowing arbitrarily close representatives
when the distance infimum is not attained. This proves (CONF).

No numeric R or basin δ is supplied. This is an all-time confinement theorem
near exact two-dimensional minimizers, not a finite lifetime estimate for
the D4 numerical branch or a theorem in four spatial dimensions.

## 7. Spectrum and the boundary of the conclusion

For a **real** exact profile, L_−=A²−ω−βQ²+βQ⁴,
L_+=A²−ω−3βQ²+5βQ⁴ and the real generator is
J L=[[0,L_−],[−L_+,0]]. Its natural L² domain is H⁴⊕H⁴;
the quadratic form domain is H²⊕H². Phase gives L_−Q=0 and translations
give L_+∂_jQ=0 when these profiles are real. Complex minimizers require the
full real Hessian; reality has not been proved and is not assumed in (ORB).
At a global minimizer, the Hessian of H−ωM is nonnegative on the mass tangent
space by the second variation along mass-normalized curves.

The limiting free operator has dispersion ±i((1−|ξ|²)²−ω), with ω<0.
Decaying bounded nonlinear coefficients are relatively compact perturbations
of the elliptic resolvent, so this identifies the essential spectrum for an
exact localized profile. It does not certify discrete point spectrum of the
computed branch. No exhaustive spectral enclosure is produced here.

If an isolated unstable eigenvalue were rigorously established for a specified
profile, a logarithmic exit estimate would additionally require excitation
of that mode, a spectral splitting with controlled semigroup bounds, a
quadratic remainder estimate in a well-posed norm, and control until the
chosen observable crosses its exit threshold. None is supplied for the
periodic numerical branch. A coarse-mesh eigenvalue is not such a theorem.

There is no comparable R³/R⁴ dataset or fixed four-dimensional model here.
The 3D-versus-4D lifetime hypothesis remains OPEN; the symbol D4 supplies
no dimension-specific evidence for it.

## 8. Formal dependency status

The original 28 D4Binding theorems are preserved byte-for-byte. New scalar
lemmas verify the rational slack, Gaussian sign and lower-bound algebra,
and construct a BindingSequenceInputs value from explicitly displayed
negative-infimum and adjusted-profile premises. That constructor removes
the formerly packaged amplitude-ratio obligation from callers, but its
Sobolev/sequence premises still need a concrete H² Lean instance.

Sections 1–5 discharge those premises in conventional mathematical analysis.
Lean still lacks concrete Sobolev/Fourier/change-of-variable instances,
the actual adjusted sequence construction, Brezis–Lieb/Rellich application,
and the global PDE flow instance. These are **formalization obligations**,
not assumptions inferred from numerical tests. The conditional kernel theorem
must continue to be labelled conditional until those instances compile.
