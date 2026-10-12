# Lean formalization: five-point nonmixed-gap packing

This package formalizes the exact `k=m=2` density formula for every pair of coprime positive integers `a,b`, using Lean 4.19.0 and mathlib v4.19.0. It does not claim the general `k,m` conjecture or publication priority.

The main theorem is `W01.packingDensity_formula_euclidean` in `W01/Main.lean`. Its only hypotheses are positivity and `Nat.Coprime a b`. The quotient and remainder are the integer expressions `((a : ℤ)-b)/5` and `((a : ℤ)-b)%5`, so negative quotients are retained. `targetDensity` is the three-branch formula

| Remainder | Density |
|---|---|
| `0` | `1/5` |
| `1,2` | `(b+2q)/(2a+3b)` |
| `3,4` | `(a-2(q+1))/(3a+2b)` |

`IsPacking` means pairwise disjoint translates of the original five-point set `{0,a,2a,2a+b,2a+2b}`. `upperDensity` is the symmetric-interval limsup of center counts. The theorem `symmetricRatio_eq_original` identifies the implementation with `|A ∩ [-N,N]|/(2N+1)`. `packingDensity` takes the supremum over all `A : Set ℤ`, without a periodicity or density-limit hypothesis. The proof also supplies explicit constructions whose symmetric ratios converge to the asserted values.

## Proof components

| Module | Kernel-checked content |
|---|---|
| `Basic` | Exact shape/difference/avoidance correspondence; six path cliques |
| `Density` | Original interval counts and limsup; local good blocks imply a global bound |
| `Equality` | Path saturation implies the parity representation at every integer starting point |
| `PathAverage` | All-parameter path identity, local bound, and equality saturation |
| `Arithmetic` | Four nonzero remainder alternatives and fraction comparisons |
| `Upper` | Upper bound for every packing center set, including nonperiodic sets |
| `Lower` | Signed-quotient construction, collision exclusion, periodicity, and packing |
| `PeriodicDensity` | Exact periodic-window counts imply a genuine symmetric density limit |
| `LowerCount` | Counts and density limits for both nonzero construction branches |
| `Zero` | Period-five construction and exact density for the zero branch |
| `Main` | Attainment, supremum equality, and the Euclidean-division formulation |

All principal theorem axiom reports, including both final formula theorems, contain only the standard Lean axioms `propext`, `Classical.choice`, and `Quot.sound` (or a subset). There are no placeholder proofs, additional mathematical axioms, unsafe declarations, or native-evaluation shortcuts in this package. The formulas are proved symbolically for all parameters; finite numerical checks are not imported.

## Reproducing the recorded check

The recorded build uses the existing Lean executable and already compiled dependency packages. `build.ps1` reads those dependencies and compiles the modules sequentially into this package's `.lake/build/lib/lean` directory. Pass the Lean 4.19.0 executable and the directory containing the pinned dependency packages:

```powershell
pwsh ./build.ps1 -LeanExecutable <lean-executable> -PackageRoot <dependency-packages-directory>
```

The final `BUILD_SUCCEEDED` marker and the theorem signatures/axiom reports are in `KERNEL_CHECK.txt`. The dependency manifest pins mathlib to `c44e0c8ee63ca166450922a373c7409c5d26b00b` and records its transitive revisions. Standard Lake project files are also included; the recorded verification used the direct compiler script above, rather than a fresh dependency download.

## Attribution

The mathematical source is Alexander Natalchenko and Arsenii Sagdeev, *Packing Density of Sets With Only Two Nonmixed Gaps*, Journal of Graph Theory 110 (2025), no. 3, 263–271, [DOI:10.1002/jgt.23269](https://doi.org/10.1002/jgt.23269), [arXiv:2407.01101v2](https://arxiv.org/abs/2407.01101v2). Their Theorem 2 and Section 2 supply the periodic lower constructions and the zero-remainder equality. The present formal proof specializes those constructions and verifies the complete upper bound for `k=m=2`.

Lean and mathlib are third-party dependencies distributed under their own Apache 2.0 licenses. Their source distributions, licenses, and attribution are not replaced by this package; dependencies and the source article are not redistributed here. This work was developed with AI assistance in the mathematical argument, exposition, and formal proof code.

The public files are exactly those in `PUBLIC_FILES.txt`; `SHA256SUMS` hashes all listed files except itself.
