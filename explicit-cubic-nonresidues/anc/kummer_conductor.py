# kummer_conductor.py -- empirical conductor of K = F(a^{1/3}) over F = Q(sqrt-3) (Lemma 10.1: f(K/F) | 9a).
# For each a, the least k such that p -> (a/p)_3 is constant on ray classes modulo lambda^k * prod_{q | a, q != lambda} q,
# tested on all prime ideals p of norm <= 60000 with p not dividing 3a; and whether each tame prime q | a is needed.
# Prints one summary line; -v prints each a.
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from zw import *  # noqa: E402

V = '-v' in sys.argv
PR = prime_elements(60000)


def lam_power(k):
    r = ONE
    for _ in range(k):
        r = mul(r, LAM)
    return r


def factor_primes(a):
    return [q for q in PR if norm(q) <= norm(a) and divides(q, a)]


def consistent(sym, m):
    R = IdealMod(m)
    seen = {}
    for p, v in sym:
        key = min(R.red(mul(u, p)) for u in UNITS)
        if key in seen and seen[key] != v:
            return False
        seen[key] = v
    return True


avals = [(2, 0), (3, 0), (5, 0), (6, 0), (7, 0), (10, 0), (4, 0), (12, 0), LAM, W, (2, 1), (1, 3), (-3, 0), (9, 0), (2, 6), (5, 3), (1, 9), (4, 3)]
ok = True
kmax = 0
attained = []
for a in avals:
    qs = [q for q in factor_primes(a) if not divides(q, LAM) and not divides(LAM, q)]
    sym = [(p, cubic_symbol(a, p)) for p in PR if norm(p) % 3 != 0 and not divides(p, a)]
    qprod = ONE
    for q in qs:
        qprod = mul(qprod, q)
    res = [consistent(sym, mul(lam_power(k), qprod)) for k in range(0, 6)]
    kmin = min((k for k in range(6) if res[k]), default=None)
    tame = []
    for q in qs:
        rest = ONE
        for q2 in qs:
            if q2 != q:
                rest = mul(rest, q2)
        tame.append(not consistent(sym, mul(lam_power(kmin if kmin is not None else 5), rest)))
    good = kmin is not None and kmin <= 4 and all(res[kmin:]) and all(tame)
    ok = ok and good
    if kmin is not None:
        kmax = max(kmax, kmin)
        if kmin == 4:
            attained.append(a)
    if V:
        print(f"a={a} N(a)={norm(a)}: tame primes {qs} (each needed: {tame}); consistent mod lambda^k for k=0..5: {res} -> lambda-exponent {kmin}")
print(f"kummer_conductor: {'OK' if ok else 'FAIL'}; {len(avals)} values of a, prime ideals of norm <= 60000: lambda-exponent of f(F(a^(1/3))/F) always <= 4 = v_lambda(9) (max {kmax}, attained for a in {attained}); every tame prime q | a enters with exponent 1 and is needed; hence f | 9a in every case")
