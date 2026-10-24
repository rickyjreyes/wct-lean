# Frozen D4 formalization boundary

Canonical source: geometry_of_resonance PR36, head
31f322c94d2ef32b20acea741884514806025c85, merge
5a4c58a4206005ad9d46ee2951069186490b01f1.

The source file formalizes exact dyadic parameters, the threshold comparison,
square completion, dilation minimization, virial algebra, the improved D bound,
amplitude comparison, passage through an adjusted minimizing sequence, and
strict energy per mass implying all-split binding. Build status is recorded
separately; the presence of declarations is not itself verification.

`WholeSpaceData` names the uninstantiated H² carrier and weak Laplacian. The
integrals are on the two-dimensional whole plane, with the full kinetic
coefficient. `BindingSequenceInputs` explicitly requires negativity, adjusted
minimizing sequences, their ratio estimate and admissible amplitude trials.
It does not assume strict binding, an attained infimum, or numerical stability.

OPEN: instantiate these inputs using actual Sobolev/Fourier/change-of-variable
analysis; exclusion of vanishing and dichotomy; concentration compactness modulo
translations; minimizer existence; Euler–Lagrange regularity; global H² flow;
orbital stability of the entire minimizing set. No finite-dimensional toy model
is substituted. Periodic-root identification and S004 completion remain separate.
