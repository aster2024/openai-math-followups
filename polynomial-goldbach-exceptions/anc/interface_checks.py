#!/usr/bin/env python3
"""Exact checks of the physical scales and the two analytic interfaces."""
from fractions import Fraction as F
from itertools import product
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def main():
    # The transfer exponents, before arbitrary small powers and logarithms.
    assert -2 + F(5, 4) + 1 == F(1, 4)
    assert -2 + F(19, 24) + F(3, 2) == F(7, 24)
    assert [d * F(1, 4) for d in (2, 3)] == [F(1, 2), F(3, 4)]
    assert [d * F(7, 24) for d in (2, 3)] == [F(7, 12), F(7, 8)]

    # Perelli--Pintz (3.10), and the same Holder inequality with K
    # restricted to E exceptional values: the E^(1/2) factor is retained.
    full_parameter = 2 * (F(19, 48) + F(3, 4) + F(1, 4) - 1)
    exceptional_parameter = 4 * (F(19, 48) + F(3, 4) - 1)
    assert (full_parameter, exceptional_parameter) == (F(19, 24), F(7, 12))

    nu = F(1, 144)
    pmin, pmax = F(4, 9) - 2 * nu, F(4, 9) - nu
    assert (pmin, pmax) == (F(31, 72), F(7, 16))
    assert pmin > F(5, 12)
    assert 1 - pmin / 2 == F(113, 144) < F(19, 24)
    # For Y=X^lambda, lambda<=1, the first term costs
    # (1+lambda-pmin)/2 <= 1-pmin/2. This tests the affine identity.
    for lam in (F(1, 100), F(1, 4), F(1, 2), F(99, 100), F(1)):
        assert (1 + lam - pmin) / 2 <= 1 - pmin / 2
    assert F(1, 2) < F(19, 24)  # proper prime powers

    # Enumeration is finite supporting evidence for the coefficient lemma.
    # The proof for all X is the three-value calculation in the paper.
    triples = 0
    zero_norm = negative_norm = 0
    for size in range(2, 21, 2):
        for y0, y1, y2 in product(range(size // 2, size + 1), repeat=3):
            a = F(y2 - 2 * y1 + y0, 2)
            if not a or a.denominator != 1:
                continue
            b, c = y1 - y0 - a, F(y0)
            assert abs(a) <= F(size, 2) and abs(b) <= size and abs(c) <= size
            assert [a*j*j+b*j+c for j in range(3)] == [y0, y1, y2]
            for target in range(size, 2*size+1):
                norm = 4*a*target + 2*b*b - 8*a*c
                assert abs(norm) <= 10*size*size
                zero_norm += norm == 0
                negative_norm += norm < 0
            triples += 1
    assert zero_norm and negative_norm

    # All smaller zero-free boundaries use the same LL delta=1/8.
    tracker = F(4369779, 5000000)
    assert tracker < F(7, 8) < F(11, 12)
    assert 1-max(tracker, F(7, 8)) == F(1, 8)

    out = {"status": "PASS", "coefficient_triples": triples,
           "zero_norm_instances": zero_norm,
           "negative_norm_instances": negative_norm,
           "physical_exponents": ["1/4", "7/24"],
           "PP_parameter_exponents": [str(full_parameter), str(exceptional_parameter)],
           "minor_arc_prefix_exponent": "113/144 < 19/24",
           "tracker_boundary": str(tracker),
           "scope": "Exact algebra and finite examples; analytic inputs remain cited theorems."}
    (ROOT / "results").mkdir(parents=True, exist_ok=True)
    (ROOT / "results/interface_checks.json").write_text(json.dumps(out, indent=2)+"\n")
    print(f"PASS interface_checks: PP 19/24 to 7/12, {triples} coefficient triples, and prefix bounds")


if __name__ == "__main__":
    main()
