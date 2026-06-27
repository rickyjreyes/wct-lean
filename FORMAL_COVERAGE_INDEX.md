# WCT Lean Formal Coverage Index

This page separates the **complete 142-object WCT equation registry** from the smaller subset that currently has direct or supporting Lean declarations.

## Canonical navigation

- [Full corrected equation registry](https://github.com/rickyjreyes/geometry_of_resonance/blob/main/WCT_FULL_EQUATION_LIST_CORRECTED.md)
- [Master equation architecture](https://github.com/rickyjreyes/geometry_of_resonance/blob/main/WCT_MASTER_EQUATIONS_UPDATED.md)
- [Complete SymPy classification of all 142 objects](https://github.com/rickyjreyes/wct-sympy/blob/main/VERIFICATION_INDEX.md)
- [Lean theorem inventory](THEOREMS.md)
- [SymPy-to-Lean relationship map](SYMPY_MAP.md)
- [Public cross-repository corpus map](https://rickyjreyes.github.io/research-corpus/)

The canonical registry defines the equation text, symbols, assumptions, and scientific boundary. Lean only claims what is accepted by the kernel under the hypotheses written in each declaration.

## Registry accounting

The complete WCT registry contains 142 objects. The current Lean repository has direct or supporting mappings for 18 canonical IDs; the other 124 objects have no direct completed Lean mapping in the maintained index.

## IDs with direct or supporting Lean declarations — 18

`E1A E1B E2 E3 E5 E6 E7 E9 E13 E14 E17 E18 E58 E78 CM9 CM12 CM13 CM16`

These do not all have the same strength:

- `E1A`, `E1B`, `E6`, `E7`: dimensional support only.
- `E2`, `E3`, `E5`, `E9`, `E18`, `E58`, `CM9`: kernel-checked algebraic or order-theoretic support under displayed hypotheses.
- `E13`, `E14`: one-mode or positivity support, not the full generalized variational theorem.
- `E17`: counterexample to the historical scalar denominator plus restricted-sector repairs; the complete complex operator remains open.
- `E78`: adjacent TODO proposition, not a proof.
- `CM12`, `CM13`, `CM16`: definitions, not theorem-level physical validation.

See [`THEOREMS.md`](THEOREMS.md) for declaration names and exact boundaries.

## Registry IDs without a direct completed Lean mapping — 124

`M1 M2 M3 M4 M5 M6A M6B M7 M8 E4 E8 E10 E11 E12 E15 E16 E19 E20 E21 E22`

`E23 E24 E25 E26 E27 E28 E29 E30 E31 E32 E33 E34 E35 E36 E37 E38 E39 E40 E41 E42`

`E43 E44 E45 E46 E47 E48 E49 E50 E51 E52 E53 E54 E55 E56 E57 E59 E60 E61 E62 E63`

`E64 E65 E66 E67 E68 E69 E70 E71 E72 E73 E74 E75 E76 E77 E79 E80 E81 E82 CLE1 CLE2`

`CLE3 CLE4 CLE5 CLE6 CLE7 CLE8 CLE9 CLE10 G1 EX EY EZ FA CM1 CM2 CM3 CM4 CM5 CM6 CM7`

`CM8 CM10 CM11 CM14 CM15 CM17 CM18 CM19 CM20 TOP1 TOP2 TOP3 TOP4 TOP5 TOP6 TOP7 TOP8 TOP9 CORR1 CORR2`

`CORR3 CORR4 CORR5 CORR6`

“No direct completed Lean mapping” does not mean false. It means this repository does not currently expose a maintained kernel-checked declaration that closes that canonical object.

## Status rule

- `PROVED`: the Lean kernel accepts the declaration under displayed hypotheses.
- `COUNTEREXAMPLE`: Lean proves a concrete contradiction to an unrestricted or historical claim.
- `CONDITIONAL`: named assumptions are required.
- `DEFINITION`: an object is introduced without proving a property.
- `TODO` or `OPEN`: no completed Lean theorem closes the obligation.

A SymPy `PASS` must never be reported as a Lean proof, and a Lean proof must never be reported as empirical validation.
