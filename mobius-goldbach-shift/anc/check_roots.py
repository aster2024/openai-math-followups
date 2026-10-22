#!/usr/bin/env python3
"""Exact small root counts, matrix-line counts and local factors."""
from collections import Counter
from fractions import Fraction
from math import gcd


def prime_factors(n):
    result = []
    for p in range(2, n + 1):
        if n % p == 0 and all(p % d for d in range(2, int(p ** 0.5) + 1)):
            result.append(p)
    return result


def kernel(row, p):
    a, b = row
    return (1, -a * pow(b, -1, p) % p) if b % p else (0, 1)


def main():
    roots = branches = matrix_classes = local_tests = 0
    seen_branches = Counter()
    for total in (2, 4, 6, 10, 12, 30):
        fast, direct = Counter(), Counter()
        mod = 5 if total % 5 else 7
        for u in range(2, 43):
            if gcd(u, total) != 1:
                continue
            for v in range(2, 51):
                if gcd(u, v) != 1 or gcd(v, total) != 1:
                    continue
                c = -total * pow(v, -1, u) % u
                d = (total + c * v) // u
                assert u * d - c * v == total
                fast[(u % mod, c % mod, v % mod, d % mod)] += 1
                roots += 1
                for cc in range(u):
                    if (total + cc * v) % u == 0:
                        dd = (total + cc * v) // u
                        direct[(u % mod, cc % mod, v % mod, dd % mod)] += 1
                        assert (cc, dd) == (c, d)
                if total < u * v:
                    k = d // v
                    cs, ds = (1 + k) * v - d, (1 + k) * u - c
                    beta = Fraction(c, u)
                    eps = Fraction(total, u * v)
                    assert k in (0, 1)
                    assert Fraction(cs, v) == 1 + k - beta - eps
                    assert 0 < cs < v and v * ds - u * cs == total
                    assert cs == -total * pow(u, -1, v) % v
                    seen_branches[k] += 1
                    branches += 1
        assert fast == direct
        # c_N / zeta(2)^(-1), checked by exact finite residue densities.
        factors = prime_factors(total)
        ratio = Fraction(1)
        for p in factors:
            ratio *= Fraction(p - 1, p + 1)
            pair_count = sum(gcd(a * b, p) == 1 for a in range(p) for b in range(p))
            density = Fraction(pair_count, p * p)
            assert density / (1 - Fraction(1, p * p)) == Fraction(p - 1, p + 1)
            assert Fraction(p - 1, p + 1) == (1 - Fraction(1, p)) ** 2 / (1 - Fraction(1, p * p))
            local_tests += 1
        assert 0 < ratio <= 1
    assert set(seen_branches) == {0, 1}
    for p in (2, 3, 5, 7):
        for target in range(1, p):
            lines = Counter()
            for a in range(p):
                for b in range(p):
                    for c in range(p):
                        for d in range(p):
                            if (a * d - b * c) % p == target:
                                lines[kernel((a, b), p)] += 1
            assert len(lines) == p + 1
            assert set(lines.values()) == {p * (p - 1)}
            assert sum(lines.values()) == p * (p * p - 1)
            matrix_classes += sum(lines.values())
    print(f'Lemma R algebra: PASS; roots={roots}; swapped={branches}; '
          f'branches={dict(sorted(seen_branches.items()))}; '
          f'matrices={matrix_classes}; local_factors={local_tests}')


if __name__ == '__main__':
    main()
