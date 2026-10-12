#!/usr/bin/env python3
"""Finite exact checks for the two-by-two nonmixed-gap packing theorem.

Run: python verify.py > results.json
Python 3.8+; standard library only. These checks do not prove the infinite
parameter theorem or its upper bound for arbitrary infinite center sets.
The periodic construction is due to A. Natalchenko and A. Sagdeev,
Packing Density of Sets With Only Two Nonmixed Gaps, Theorem 2 and Section 2,
arXiv:2407.01101v2; DOI:10.1002/jgt.23269.
"""
from collections import Counter
from itertools import accumulate, combinations
import json
from math import gcd


def check(condition, message):
    if not condition:
        raise AssertionError(message)


def shape(a, b):
    return (0, a, 2 * a, 2 * a + b, 2 * a + 2 * b)


def differences(a, b):
    return {y - x for x, y in combinations(shape(a, b), 2)}


def density_ratio(a, b):
    q, r = divmod(a - b, 5)
    if r == 0:
        return 1, 5
    if r <= 2:
        return b + 2 * q, 2 * a + 3 * b
    return a - 2 * (q + 1), 3 * a + 2 * b


def check_paths(a, b):
    d = differences(a, b)
    check(d == {i * a + j * b for i in range(3) for j in range(3)
                if i + j > 0}, "five-point difference set")
    actual = Counter()
    # Choosing positions retains six words with multiplicities when a = b.
    for positions in combinations(range(4), 2):
        steps = [a if i in positions else b for i in range(4)]
        points = [0] + list(accumulate(steps))
        check(all(y - x in d for x, y in combinations(points, 2)), "path clique")
        for shift in range(steps[-1]):
            actual.update(shift + point for point in points)
    n1, n2 = 2 * a + 3 * b, 3 * a + 2 * b
    check(actual == Counter({x: 3 * (int(x < n1) + int(x < n2))
                             for x in range(max(n1, n2))}), "path identity")


def check_construction(a, b):
    numerator, denominator = density_ratio(a, b)
    reverse_n, reverse_d = density_ratio(b, a)
    check(numerator * reverse_d == reverse_n * denominator, "symmetry")
    q, r = divmod(a - b, 5)
    if r == 0:
        period, residues = 5, [0]
    else:
        x, y = (a, b) if r <= 2 else (b, a)
        quotient, remainder = divmod(x - y, 5)
        check(remainder in (1, 2), "reflected remainder")
        period = 2 * x + 3 * y
        count = y + 2 * quotient
        check(count > 0, "positive construction size")
        residues = [(t * (x - y)) % period for t in range(count)]
    check(len(set(residues)) == len(residues), "distinct center residues")
    covered = [(center + point) % period
               for center in residues for point in shape(a, b)]
    check(len(set(covered)) == 5 * len(residues), "disjoint translates modulo period")
    check(len(residues) * denominator == numerator * period, "construction density")


def independent_sets(candidates, forbidden, chosen=()):
    """Each set occurs once, at the node for its increasing vertex sequence."""
    yield chosen
    for index, vertex in enumerate(candidates):
        remaining = tuple(x for x in candidates[index + 1:]
                          if x - vertex not in forbidden)
        yield from independent_sets(remaining, forbidden, chosen + (vertex,))


def check_local(a, b):
    n1, n2 = 2 * a + 3 * b, 3 * a + 2 * b
    q, r = divmod(a - b, 5)
    total = equalities = 0
    for selected in independent_sets(tuple(range(n2)), differences(a, b)):
        total += 1
        f1, f2 = sum(x < n1 for x in selected), len(selected)
        check(f1 + f2 <= a + b, "weighted interval inequality")
        if f1 + f2 == a + b:
            equalities += 1
            t = sum(b <= x < a for x in selected)
            check(t == sum(a + b <= x < 2 * a for x in selected), "equal hole counts")
            check(f1 == b + 2 * t and f2 == a - 2 * t, "equality representation")
        if r in (1, 2):
            check(f1 <= b + 2 * q or f2 <= b + 3 * q, "local alternative 1/2")
        if r in (3, 4):
            check(f1 <= a - 3 * (q + 1) or f2 <= a - 2 * (q + 1),
                  "local alternative 3/4")
    return {"a": a, "b": b, "interval_length": n2,
            "independent_sets": total, "equality_cases": equalities}


def main():
    path_count = construction_count = 0
    for a in range(1, 65):
        for b in range(1, 65):
            check_paths(a, b)
            path_count += 1
            if gcd(a, b) == 1:
                check_construction(a, b)
                construction_count += 1
    local = [check_local(a, b) for a in range(2, 9) for b in range(1, a)]
    result = {
        "arithmetic": "arbitrary-precision integers; no floating point",
        "scope": "finite checks only; the all-parameter theorem requires the written proof",
        "path_parameter_range": "1 <= a,b <= 64, all ordered pairs",
        "path_identity_pairs": path_count,
        "construction_parameter_range": "1 <= a,b <= 64, gcd(a,b) = 1",
        "periodic_construction_pairs": construction_count,
        "local_parameter_range": "1 <= b < a <= 8, no coprimality or origin condition",
        "local_parameter_pairs": len(local),
        "independent_sets": sum(case["independent_sets"] for case in local),
        "equality_cases": sum(case["equality_cases"] for case in local),
        "local_details": local,
        "all_checks_passed": True,
    }
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
