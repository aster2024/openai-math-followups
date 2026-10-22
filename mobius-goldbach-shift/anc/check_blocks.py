#!/usr/bin/env python3
"""Finite exact checks of the block algebra; no asymptotic claims."""
from collections import defaultdict
from fractions import Fraction
from math import gcd


def det(a, b):
    return a[0] * b[1] - a[1] * b[0]


def basis(total, u, v):
    c = (-total * pow(v, -1, u)) % u if u > 1 else 0
    return (c, (total + c * v) // u)


def image(p, q, z):
    return tuple(z[0] * p[i] + z[1] * q[i] for i in (0, 1))


def main():
    counts = defaultdict(int)
    primitive_z = [(a, b) for a in range(-2, 3) for b in range(-2, 3)
                   if gcd(a, b) == 1]
    for total in range(2, 25, 2):
        units = [a for a in range(total) if gcd(a, total) == 1]
        slopes = defaultdict(int)
        for u in units:
            for v in units:
                slopes[v * pow(u, -1, total) % total] += 1
        assert len(slopes) == len(units)
        assert set(slopes.values()) == {len(units)}
        counts['unit_chart'] += len(units) ** 2
        for u in range(1, 19, 2):
            for v in range(1, 19, 2):
                if gcd(u, v) != 1 or gcd(u * v, total) != 1:
                    continue
                p = (u, v)
                q = basis(total, u, v)
                assert det(p, q) == total
                assert (q[1] * u - v * q[0]) % total == 0
                for z in primitive_z:
                    qz = image(p, q, z)
                    assert det(p, qz) == total * z[1]
                    assert gcd(*qz) == 1 if gcd(qz[0], total) == 1 else gcd(*qz) > 1
                    # In the sheared basis endpoint parity is z1+c' z2, not z1.
                    odd = qz[0] % 2 == qz[1] % 2 == 1
                    assert odd == ((z[0] + q[0] * z[1]) % 2 == 1)
                    for w in primitive_z[:4]:
                        assert det(qz, image(p, q, w)) == total * det(z, w)
                        counts['determinants'] += 1
                    counts['new_basis_parity'] += 1
                counts['bases'] += 1
        # Integer-lattice block counting, including the additive 1.
        for slope in units:
            pts = []
            for a in range(2, 33):
                for b in range(3, 7):
                    if (b - slope * a) % total == 0:
                        rel = (a, (b - slope * a) // total)
                        if gcd(*rel) == 1:
                            pts.append((a, b))
            if pts:
                p0 = pts[0]
                by_det = defaultdict(list)
                for q in pts:
                    by_det[det(p0, q)].append(q)
                assert max(map(len, by_det.values())) <= 16
                assert len(pts) <= 16 * (2 * (64 * 2 * 3 // total) + 1)
                counts['counted_blocks'] += 1
    # Small explicit cases of the block parity and of a labelled overlap.
    assert basis(2, 3, 1) == (1, 1)
    assert image((3, 1), (1, 1), (0, 1)) == (1, 1)
    assert (9 - 1 * 3) % 6 == (9 - 5 * 3) % 6 == 0
    # The small-shift oriented basis and both parity cases.
    for h in list(range(-9, 0)) + list(range(1, 10)):
        for u, v in ((3, 1), (5, 3), (7, 5)):
            if gcd(u * v, h) != 1:
                continue
            c, d = basis(1, u, v)
            p, q = (u, v), (-h * c, -h * d)
            assert det(p, q) == -h
            for z in primitive_z:
                qz = image(p, q, z)
                tau = Fraction(z[0]) - h * Fraction(c, u) * z[1]
                assert qz[1] == v * tau - Fraction(h * z[1], u)
                odd = qz[0] % 2 == qz[1] % 2 == 1
                test = z[0] % 2 == 1 and (h % 2 == 0 or z[1] % 2 == 0)
                assert odd == test
                counts['small_shift_parity'] += 1
    # Exact Gaussian-integer coefficients: square positivity and conjugation.
    total = 10
    sums = defaultdict(complex)
    entries = []
    for a in (3, 7):
        for m in range(1, 12):
            for n in range(1, 12):
                if gcd(m * n, total) != 1 or (total - m * n) % a:
                    continue
                h = (total - m * n) // a
                assert h != 0
                alpha, beta = (1j) ** m, (n % 3 + 1) * (1j) ** n
                sums[h] += alpha * beta
                entries.append((a, m, n, h, alpha, beta))
    positive = sum(abs(v) ** 2 for h, v in sums.items() if h > 0)
    all_integer = sum(abs(v) ** 2 for v in sums.values())
    expanded = sum((a[4] * a[5]) * (b[4] * b[5]).conjugate()
                   for a in entries for b in entries if a[3] == b[3])
    assert abs(expanded - all_integer) < 1e-10 and positive <= all_integer
    for a, m, n, h, am, bn in entries:
        for b, r, s, hh, ar, bs in entries:
            f_p, f_q = am.conjugate() * bs, ar.conjugate() * bn
            assert f_p.conjugate() * f_q == am * ar.conjugate() * bn * bs.conjugate()
            if gcd(a, b) == 1:
                assert (h == hh) == (b * m * n - a * r * s == total * (b - a))
            counts['pairings'] += 1
    print('block algebra: PASS; ' + '; '.join(f'{k}={v}' for k, v in sorted(counts.items())))


if __name__ == '__main__':
    main()
