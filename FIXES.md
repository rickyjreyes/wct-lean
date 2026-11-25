# Lean Project Fixes Summary

## Problem 1: Incorrect Directory Structure

**Before:** All `.lean` files were in the root directory  
**After:** Files organized into proper module hierarchy:

```
MyProject/
├── Basic.lean
├── Falsification.lean
├── Theta/
│   ├── Core.lean        ← NEW: Single source of truth
│   ├── Definitions.lean
│   ├── Entropy.lean
│   ├── Dynamics.lean
│   └── Baselines.lean
└── LeanTests/
    ├── Sanity.lean
    ├── EntropyMonotone.lean
    ├── Attractor.lean
    └── DimensionFailure.lean
```

## Problem 2: Massive Duplicate Definitions

The following were defined **multiple times** across different files, causing conflicts:

- `State` - redefined in 4+ files
- `ThetaParams` - redefined in 4+ files  
- `Theta` - redefined in 4+ files
- `Entropy` - redefined in 3+ files
- `IsAttractor` - redefined in 4+ files
- `EntropyMonotoneTheta` - redefined in 2+ files
- `WCT_Falsified` - defined in both `Basic.lean` and `Falsification.lean`

**Fix:** Created `MyProject/Theta/Core.lean` as the **single source of truth** for all core types:

`ThetaModel` supplies the state type, step map, entropy and energy as explicit model data. `IsFixedPoint`, `IsAttractingFixedPoint`, `IsLyapunovStable` and `IsAsymptoticallyStable` distinguish distinct mathematical properties. Model-specific physical realization and orbital stability remain OPEN; function totality is not PDE well-posedness. Other legacy modules import Core rather than reintroducing global model assumptions.

## Problem 3: WCT_Falsified Conflict

**Before:** Defined as `False` in `Basic.lean` AND with a proper definition in `Falsification.lean`  
**After:** Removed from `Basic.lean`, kept only in `Falsification.lean` with the proper definition.

## Problem 4: Syntax Issues

- Fixed `Theta p != applyBaseline B` to `Theta p ≠ applyBaseline B` in `Baselines.lean`
- Ensured consistent Unicode symbols throughout

## Import Hierarchy (Dependency Order)

```
Mathlib
    │
    ▼
MyProject.Basic ─────────────────────────────────┐
                                                 │
MyProject.Theta.Core                             │
    │                                            │
    ▼                                            │
MyProject.Theta.Definitions                      │
    │                                            │
    ├──────────────┬──────────────┐              │
    ▼              ▼              ▼              │
Entropy       Dynamics      Baselines           │
    │              │                             │
    ▼              ▼                             │
EntropyMonotone  Attractor                      │
    │                                            │
    ▼                                            │
Falsification ◀──────────────────────────────────┘
    │
    ▼
MyProject.lean / Main.lean
```

## To Build

```bash
lake update
lake build
```
