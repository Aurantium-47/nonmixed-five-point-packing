# The packing density of five integers with gaps a, a, b, b

This note proves the complete `k=m=2` parameter family of the nonmixed-gap packing conjecture of Natalchenko and Sagdeev. The parameters `a,b` are arbitrary coprime positive integers. Density is the symmetric-interval limsup of translation centers, including arbitrary nonperiodic center sets.

Writing `a-b=5q+r` with `0 <= r <= 4`, the exact density is

| Remainder | Density |
|---|---|
| `r=0` | `1/5` |
| `r=1,2` | `(b+2q)/(2a+3b)` |
| `r=3,4` | `(a-2(q+1))/(3a+2b)` |

The matching lower-bound constructions are due to the source authors. This note supplies a self-contained proof and makes no publication-priority claim. It does not settle the general `k,m` conjecture. The mathematical proof does not depend on computation or on completion of a proof-assistant formalization.

- `main.pdf`: complete English proof, 7 pages.
- `main.tex`: standalone source, with its bibliography included.
- `SUMMARY_zh.md`: Chinese summary.
- `PROOF_PACKAGE.md`: explicit assumptions, proof dependencies, and proof outline.
- `REFERENCES.md`: sources, attribution, and third-party license boundaries.
- `VERIFICATION.md`: finite verification scope and reproducibility details, including the correction needed by an earlier Windows verifier.
- `validation/verify.py` and `validation/results.json`: minimal exact verification program and its actual output.
- [`formalization/README.md`](formalization/README.md): complete Lean proof, pinned dependencies, and the recorded kernel-check output.

To reproduce the checks, run `python -B validation/verify.py > validation/results.json` with Python 3.8 or later. To build the paper, run `pdflatex -interaction=nonstopmode -halt-on-error main.tex` twice. The paper uses standard LaTeX packages including Latin Modern fonts. The distributed PDF has resolved cross-references and embedded Type 1 fonts.

## Complete Lean formalization

Version 0.2.0 adds a complete formalization of the same `k=m=2` theorem in Lean 4.19.0 with mathlib v4.19.0. The final theorem, `W01.packingDensity_formula_euclidean`, covers every pair of coprime positive parameters and the supremum of the original symmetric limsup over all packing center sets, including nonperiodic sets. Its axiom dependencies are exactly `propext`, `Classical.choice`, and `Quot.sound`; the proof uses no placeholder proofs, additional mathematical axioms, or native-evaluation shortcuts.

The recorded check compiled all 12 source modules using the pinned toolchain and existing dependency caches. With those dependencies available, run from the repository root:

```powershell
pwsh ./formalization/build.ps1 -LeanExecutable <lean-executable> -PackageRoot <dependency-packages-directory>
```

See [the formalization instructions](formalization/README.md) and [kernel-check output](formalization/KERNEL_CHECK.txt). A fresh-network dependency bootstrap was not tested. The original manuscript and its finite verification materials remain the v0.1.0 versions; the complete formal proof is supplied as this later supplement.

This work was developed with AI assistance in the mathematical argument, exposition, and verification code. No human authorship or independent human review is asserted by this package.

Release contents are exactly the paths in `PUBLIC_FILES.txt`. `SHA256SUMS` covers every listed file except itself. Source-article PDFs and other third-party files are linked rather than redistributed. This version is dated October 13, 2026.
