# Finite exact verification

The all-parameter theorem is established by the written proof. The accompanying computation checks finite instances of its identities, equality constraints, local alternatives, and periodic constructions. It does not establish the infinite parameter theorem or the upper bound for arbitrary, possibly nonperiodic, center sets.

Run the self-contained standard-library program from the release directory:

```text
python -B validation/verify.py > validation/results.json
```

Python 3.8 or later is sufficient. The recorded run used Python 3.12.10 on Windows and exited with code 0. All arithmetic is exact integer arithmetic, including comparisons of density fractions by cross multiplication. There are no numerical tolerances or external packages. `validation/results.json` records the output, including the counts for each local parameter pair.

| Check | Parameter range | Completed cases |
|---|---|---:|
| Positive differences of the five-point set; six-path averaging identity and path cliques | All ordered pairs `1 <= a,b <= 64` | 4,096 |
| Periodic packing, exact density, and parameter-swap symmetry | Ordered coprime pairs `1 <= a,b <= 64` | 2,519 |
| Weighted interval bound and the four local residue alternatives | All pairs `1 <= b < a <= 8` | 28 |
| Exhaustive independent subsets of `[0,3a+2b)` for those 28 pairs | No assumption that `0` belongs to the set; no coprimality restriction | 102,681 |
| Equality representation `F1=b+2t`, `F2=a-2t`, including both parity constraints | All equality cases in the preceding enumeration | 200 |

The difference set is computed directly from `S=(0,a,2a,2a+b,2a+2b)`. For each periodic construction, the program expands every translate of `S` modulo the period and verifies that all `5|R|` covered residue classes are distinct. This checks overlaps across all periods. The local enumeration builds each set through its unique increasing sequence of selected vertices, retaining only larger vertices compatible with those already selected. Thus every independent subset occurs exactly once. Six path words are retained with multiplicity even when `a=b`.

The periodic constructions are the specialization of the lower-bound construction of Alexander Natalchenko and Arsenii Sagdeev, *Packing Density of Sets With Only Two Nonmixed Gaps*, Theorem 2 and Section 2, [arXiv:2407.01101v2](https://arxiv.org/abs/2407.01101v2), [DOI:10.1002/jgt.23269](https://doi.org/10.1002/jgt.23269). The computations do not establish priority for the upper-bound proof.

An earlier certificate verifier was rerun with one portability correction: `str(path.relative_to(ROOT))` was replaced by `path.relative_to(ROOT).as_posix()` so that serialized paths match the manifest on Windows. It is therefore not claimed that this earlier verifier passed unmodified. The public results tabulated here are produced by the self-contained program above and do not require those certificate files.
