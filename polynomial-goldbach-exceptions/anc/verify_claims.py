#!/usr/bin/env python3
"""Exact finite checks of exponents, identities, multiplicities and scales."""
from fractions import Fraction as F
from math import isqrt
import json
from pathlib import Path

import sympy as sp

OUT = Path(__file__).resolve().parent / "results/verify_claims.json"
res = {}

# 1. Transfer exponents (Lemma 3.1 / Corollary 3.2)
# E <= X^-2 D^(1/2) B2 B4^(1/2) with B2 ~ X, B4 ~ X^(5/2)
e_ll = -2 + 1 + F(5, 4)
# E <= X^-2 D^(1/2) M B2^(3/2) with M ~ X^(19/24)
e_mpr = -2 + F(19, 24) + F(3, 2)
assert e_ll == F(1, 4) and e_mpr == F(7, 24)
res["physical"] = [str(e_ll), str(e_mpr)]
res["parameter_LL"] = [str(d * e_ll) for d in (2, 3)]
res["parameter_MPR"] = [str(d * e_mpr) for d in (2, 3)]
assert res["parameter_LL"] == ["1/2", "3/4"] and res["parameter_MPR"] == ["7/12", "7/8"]

# Perelli-Pintz (3.10): sign-weighted K over all m<=N, int|K|^4 ~ N^2 ~ X.
# sum|R2| <= X^(19/48) X^(3/4) X^(1/4) -> exceptions <= X^(19/48) = N^(19/24).
pp = F(19, 48) + F(3, 4) + F(1, 4) - 1
assert pp == F(19, 48) and 2 * pp == F(19, 24)
# Same Hoelder with K restricted to E exceptions: int|K|^4 <= D E^2.
# X E <= X^(19/48) X^(3/4) E^(1/2)  ->  E <= X^(2*(19/48+3/4-1)) = X^(7/24)
restricted = 2 * (F(19, 48) + F(3, 4) - 1)
assert restricted == F(7, 24)
res["PP_vs_restricted_parameter_exponent"] = [str(2 * pp), str(2 * restricted)]

# 2. The two-prefix compatibility constraints
nu_max_a = F(19, 24) - F(7, 9)          # 7/9 + nu <= 19/24
nu_max_b = (F(4, 9) - F(5, 12)) / 2     # 4/9 - 2nu > 5/12
assert nu_max_a == F(1, 72) and nu_max_b == F(1, 72)
res["nu_bound"] = str(nu_max_a)

# 3. The illustrative kappa choice and LL Proposition 9.4
dlt = sp.symbols('delta', positive=True)
kap = sp.symbols('kappa')
d = sp.Rational(1, 2) - kap
sol = sp.solve(sp.Eq(sp.Rational(5, 2) * d / (1 + 10 * d), dlt), kap)
assert len(sol) == 1 and sp.simplify(sol[0] - (5 - 24 * dlt) / (10 - 40 * dlt)) == 0
assert F(1, 2) - F(2, 9) * F(38, 167) == F(1351, 3006)
k = F(899, 2000)
dk = F(1, 2) - k
assert F(1351, 3006) < k < F(9, 20) and k > F(4, 9)
assert F(5, 2) * dk / (1 + 10 * dk) == F(101, 1204) < F(1, 8)
assert F(9, 2) * dk == F(909, 4000) and F(38, 167) - F(909, 4000) == F(197, 668000)
lower_at_78 = (5 - 24 * F(1, 8)) / (10 - 40 * F(1, 8))
res["kappa_window_at_7_8"] = [str(max(F(1351, 3006), lower_at_78)), "9/20"]

# 4. Identities
t, a, b, c, d0, x, y = sp.symbols('t a b c d0 x y')
A = 9 * a * c - 3 * b**2
B0 = 2 * b**3 - 9 * a * b * c + 27 * a**2 * d0
assert sp.expand(27 * a**2 * (a * t**3 + b * t**2 + c * t + d0) - ((3 * a * t + b)**3 + A * (3 * a * t + b) + B0)) == 0
assert sp.expand(4 * a * (a * t**2 + b * t + c) - ((2 * a * t + b)**2 + 4 * a * c - b**2)) == 0
assert sp.expand(x**3 + y**3 + A * (x + y) - (x + y) * (x**2 - x * y + y**2 + A)) == 0


# 5. Brute-force multiplicities
def tau(n):
    n = abs(n)
    cnt = 0
    for i in range(1, isqrt(n) + 1):
        if n % i == 0:
            cnt += 1 if i * i == n else 2
    return cnt


def check_quadratic(qa, qb, qc, N):
    Q = lambda u: qa * u * u + qb * u + qc
    reps = {}
    for u in range(1, N + 1):
        for v in range(1, N + 1):
            s = Q(u) + Q(v)
            reps[s] = reps.get(s, 0) + 1
    worst = 0
    for s, r in reps.items():
        V = 4 * qa * s + 2 * qb * qb - 8 * qa * qc
        bound = 1 if V == 0 else 4 * tau(V)
        assert V >= 0 and r <= bound, (qa, qb, qc, s, r, V)
        worst = max(worst, r)
    return worst


def check_cubic(qa, qb, qc, qd, N):
    Q = lambda u: qa * u**3 + qb * u * u + qc * u + qd
    A_ = 9 * qa * qc - 3 * qb * qb
    B_ = 2 * qb**3 - 9 * qa * qb * qc + 27 * qa * qa * qd
    reps = {}
    for u in range(1, N + 1):
        for v in range(1, N + 1):
            s = Q(u) + Q(v)
            reps[s] = reps.get(s, 0) + 1
    worst = 0
    zero_case = None
    for s, r in reps.items():
        V = 27 * qa * qa * s - 2 * B_
        if V != 0:
            assert r <= 4 * tau(V), (qa, qb, qc, qd, s, r)
        else:
            H = F(-2 * qb, 3 * qa)
            lin = (H.numerator - 1) if (H.denominator == 1 and H > 0) else 0
            disc = sum(1 for X_ in range(-isqrt(max(-2 * A_, 0)) - 1, isqrt(max(-2 * A_, 0)) + 2)
                       for Y_ in range(-isqrt(max(-2 * A_, 0)) - 1, isqrt(max(-2 * A_, 0)) + 2)
                       if X_ * X_ - X_ * Y_ + Y_ * Y_ == -A_)
            assert r <= lin + disc, (qa, qb, qc, qd, s, r, lin, disc)
            zero_case = (s, r, lin, disc)
        worst = max(worst, r)
    return worst, zero_case


quad = {}
for coeffs in [(1, 0, 0), (2, 0, 0), (1, 1, 1), (3, -7, 5), (-2, 300, 11), (5, 3, -40)]:
    quad[str(coeffs)] = check_quadratic(*coeffs, 120)
res["quadratic_max_multiplicity_N120"] = quad
cub = {}
for coeffs in [(1, 0, 0, 0), (2, 0, 0, 0), (1, -60, 0, 5000000), (1, -303, 30603, 0), (3, -5, 2, 7)]:
    w, z = check_cubic(*coeffs, 120)
    cub[str(coeffs)] = {"max": w, "V0": z}
res["cubic_max_multiplicity_N120"] = cub

# 6. Uniform quadratic coefficient bounds from three values (exhaustive small X)
cnt = 0
for X in range(2, 31):
    lo = -(-X // 2)
    for y0 in range(lo, X + 1):
        for y1 in range(lo, X + 1):
            for y2 in range(lo, X + 1):
                if (y2 - 2 * y1 + y0) % 2 or y2 - 2 * y1 + y0 == 0:
                    continue
                Aq = (y2 - 2 * y1 + y0) // 2
                Bq = y1 - y0 - Aq
                Cq = y0
                assert abs(2 * Aq) <= X and abs(Bq) <= X and abs(Cq) <= X
                for s in range(X, 2 * X + 1):
                    assert abs(4 * Aq * s + 2 * Bq * Bq - 8 * Aq * Cq) <= 10 * X * X
                cnt += 1
res["uniform_triples_checked"] = cnt

# 7. Moving cubic
for M in (3, 4, 10, 57):
    vals = [2 * (2 * tt - M - 1)**3 + 6 * M**3 for tt in range(1, M + 1)]
    assert all(4 * M**3 <= v <= 8 * M**3 and v % 2 == 0 for v in vals) and len(set(vals)) == M
    assert sum(1 for u in vals for v in vals if u + v == 12 * M**3) == M

# 8. Flat-part overlap lengths (Section 2)
for n in [F(1, 2), F(3, 4), F(1)]:
    L = min(F(7, 8), n - F(1, 8)) - max(F(1, 8), n - F(7, 8))
    assert L >= F(1, 4)
for h in [F(0), F(1, 4), F(1, 2)]:
    assert F(3, 4) - h >= F(1, 4)

# 9. C_Q scale bookkeeping
for AQ in (1, 2, 17):
    CQ = 2 * (1 + AQ)
    assert AQ <= F(CQ, 2) and 2 * AQ < CQ

res["status"] = "PASS"
OUT.parent.mkdir(parents=True, exist_ok=True)
OUT.write_text(json.dumps(res, indent=2) + "\n")
print("PASS verify_claims:", json.dumps({k: res[k] for k in ("physical", "parameter_LL", "parameter_MPR", "PP_vs_restricted_parameter_exponent", "kappa_window_at_7_8", "uniform_triples_checked")}))
