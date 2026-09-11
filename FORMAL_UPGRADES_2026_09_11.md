# September 2026 Formal Upgrades

This batch adds narrow kernel-checked algebraic certificates without promoting the associated physical claims beyond their proved hypotheses.

## Toroidal selector

`torusShapeSq_le_quarter` proves

```text
eta^2 (1-eta^2) <= 1/4.
```

`torusShapeSq_eq_quarter_iff` proves equality exactly when

```text
eta^2 = 1/2.
```

On the physical branch `0 < eta < 1`, this is the algebraic selector behind `eta = 1/sqrt(2)` for the toroidal Willmore expression. The theorem does not formalize the full thin-shell asymptotic expansion.

## Finite-band Hessian maximum

`finiteBandGrowth_completedSquare` proves the exact identity

```text
R k^2 - q k^4
= R^2/(4q) - q (k^2 - R/(2q))^2
```

for `q != 0`.

For `q > 0`, `finiteBandGrowth_le_max` proves the global upper bound and `finiteBandGrowth_eq_max_iff` proves equality exactly at

```text
k^2 = R/(2q).
```

Setting `q=d^-2` recovers the WCT notation `k_star^2 = R d^2/2` and `lambda_max = R^2 d^2/4`.

## Helix curvature scale

`helixCurvatureSq_add_torsionSq` proves

```text
kappa^2 + tau^2 = 1/(R^2+p^2)
```

for a nondegenerate helix denominator. `helixAspectScaleSq_identity` proves the aspect-ratio substitution `p=n eta R` gives

```text
1/[R^2 (1+n^2 eta^2)].
```

This certifies the geometry but does not assert that the integer label is a physical particle spectrum.

## Core integrability threshold

`coreIntegrabilityExponent_iff` proves

```text
2p-2 > -1  <->  p > 1/2.
```

This is the exponent reduction used by the local radial-integrability argument. The full improper-integral theorem remains a continuum-analysis obligation.

## Constrained curvature locking

`curvatureLockStationarity_iff` proves that stationarity of

```text
w (phi' - sigma)^2 + lambda phi'
```

with nonzero weight gives

```text
phi' = sigma - lambda/(2w).
```

`curvatureLock_exact_stationary_iff` makes the important caveat explicit: exact pointwise locking is stationary precisely when the local multiplier vanishes. Thus the winding constraint generally contributes a correction unless global compatibility forces the multiplier to zero.

## Contraction margin

`perturbedContractionFactor_lt_one` proves that

```text
epsilon < L delta
```

implies

```text
1 - L delta + epsilon < 1.
```

These results live in `WCTLean/Models/FormalUpgrades.lean` and are imported by the public `WCTLean.Main` root.
