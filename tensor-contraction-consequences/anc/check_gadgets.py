import sys as _local_sys
from pathlib import Path as _local_Path
_local_sys.path.insert(0, str(_local_Path(__file__).resolve().parent))
import builtins as _builtins
_detail_lines=[]
def _detail_print(*a, **kw):
    _detail_lines.append(' '.join(map(str,a)))

"""Arithmetic checks for the gadgets of Sections 4.1 and 4.3.

1. Sliced exact gadget (Section 4.1): carry chain over L-bit slices for THR / ETHR,
   and the MOD gadget with hidden quotient q (exactly one accepting q).
   Checks carry bounds -1 <= c <= r+1 and the output against direct evaluation.
2. Hashed ETHR / MOD gadget (Section 4.3): residue mod p, membership in the
   reduced target set; one-sided error and the bad-prime count bound.
3. Enumerate small MOD truth tables (r, maximal modulus)=(1,80),(2,60),(3,20)
   and record the smallest modulus encountered for each table. This does not
   implement or verify the general Cramer/Hadamard representation construction.
These are arithmetic replays; no tensor contraction, invalid auxiliary-code,
or independently assigned input-copy check is performed by this script.
Run: nice -n 19 python3 -I check_gadgets.py
"""
import itertools, random

random.seed(20261028)


def digits(v, L, K):
    return [(v >> (k * L)) & ((1 << L) - 1) for k in range(K)]


def chain(Y, A, T, L, K):
    """carry chain for D = sum_k 2^{kL} Y[k] + A - T; returns (c_final, allzero, carries)"""
    Ad, Td = digits(A, L, K), digits(T, L, K)
    c, e, cs = 0, True, []
    for k in range(K):
        z = (Y[k] if k < len(Y) else 0) + Ad[k] - Td[k] + c
        c = z >> L  # floor division by 2^L (python >> is floor for negatives)
        e = e and (z & ((1 << L) - 1)) == 0
        cs.append(c)
    return c, e, cs


def sliced(kind, w, theta, m, x, L):
    r = len(w)
    if kind == 'MOD':
        u = [wj % m for wj in w]
        lit = list(x)
        B = max(1, (m - 1).bit_length())
    else:
        u = [abs(wj) for wj in w]
        lit = [xj if wj >= 0 else 1 - xj for wj, xj in zip(w, x)]
        B = max(1, max(uj.bit_length() for uj in u))
    Ks = -(-B // L)
    Y = [sum(((uj >> (k * L)) & ((1 << L) - 1)) * lj for uj, lj in zip(u, lit)) for k in range(Ks)]
    for k in range(Ks):
        assert 0 <= Y[k] < r * (1 << L) or r == 0
    Kst = -(-(B + (r + 2).bit_length()) // L)
    if kind in ('THR', 'ETHR'):
        T = theta + sum(abs(wj) for wj in w if wj < 0)
        # clip T into [0, r 2^B] (Section 4.1 normalization); gate function unchanged
        if T < 0:
            T = 0 if kind == 'THR' else r * (1 << B)
        if T > r * (1 << B):
            T = r * (1 << B)
        assert T < (r + 2) << B
        c, e, cs = chain(Y, 0, T, L, Kst)
        assert all(-1 <= ci <= r + 1 for ci in cs), cs
        return int(c >= 0) if kind == 'THR' else int(c == 0 and e)
    # MOD with hidden q
    th = theta % m
    A = m - th
    acc = []
    for q in range(0, 1 << (r + 1).bit_length()):  # all codes, invalid codes q>r give entry 0
        if q > r:
            continue
        c1, e1, cs1 = chain(Y, A, q * m, L, Kst)
        c2, e2, cs2 = chain(Y, A, (q + 1) * m, L, Kst)
        assert all(-1 <= ci <= r + 1 for ci in cs1 + cs2)
        if c1 >= 0 and c2 < 0:
            acc.append((q, int(c1 == 0 and e1)))
    assert len(acc) == 1, acc
    return acc[0][1]


def direct(kind, w, theta, m, x):
    s = sum(wj * xj for wj, xj in zip(w, x))
    if kind == 'THR':
        return int(s >= theta)
    if kind == 'ETHR':
        return int(s == theta)
    return int((s - theta) % m == 0)


n_checks = 0
for trial in range(1500):
    r = random.randint(1, 7)
    L = random.randint(1, 5)
    B = random.randint(1, 14)
    kind = random.choice(['THR', 'ETHR', 'MOD'])
    w = [random.randint(-(1 << B) + 1, (1 << B) - 1) for _ in range(r)]
    m = random.randint(1, 1 << B)
    xs = [tuple(random.randint(0, 1) for _ in range(r)) for _ in range(6)]
    if kind == 'ETHR':  # make equality reachable sometimes
        x0 = xs[0]
        theta = sum(wj * xj for wj, xj in zip(w, x0))
    else:
        theta = random.randint(-(r + 1) << B, (r + 1) << B)
    for x in xs:
        assert sliced(kind, w, theta, m, x, L) == direct(kind, w, theta, m, x), (kind, w, theta, m, x, L)
        n_checks += 1
_detail_print('sliced gadget checks passed:', n_checks)

# 2. hashed residue gadget
def primes_above(lo, cnt):
    out, v = [], lo + 1
    while len(out) < cnt:
        if v > 1 and all(v % d for d in range(2, int(v ** 0.5) + 1)):
            out.append(v)
        v += 1
    return out

P = primes_above(8, 400)
worst = 0.0
for trial in range(300):
    r = random.randint(1, 6)
    kind = random.choice(['ETHR', 'MOD'])
    B = random.randint(4, 24)
    w = [random.randint(-(1 << B), 1 << B) for _ in range(r)]
    m = random.randint(2, 1 << B)
    theta = random.randint(-(1 << B), 1 << B)
    for x in itertools.product([0, 1], repeat=r):
        truth = direct(kind, w, theta, m, x)
        if kind == 'ETHR':
            sig = sum(wj * xj for wj, xj in zip(w, x)); targets = [theta]
        else:
            wt = [wj % m for wj in w]; sig = sum(a * b for a, b in zip(wt, x))
            targets = [theta % m + q * m for q in range(r)]
        nonzero = [sig - t for t in targets if sig != t]
        bad = 0
        for p in P:
            h = int((sig % p) in {t % p for t in targets})
            if truth == 1:
                assert h == 1
            elif h == 1:
                bad += 1
        bits = max([abs(d).bit_length() for d in nonzero] + [1])
        bound = len(targets) * bits  # each nonzero difference has < bits prime factors > 8
        assert bad <= bound, (bad, bound)
        worst = max(worst, bad / len(P))
_detail_print('hashed residue gadget: one-sided OK, bad-prime bound OK; worst bad fraction', round(worst, 4))

# 3. Lemma R for MOD on r <= 3 inputs: minimal modulus realising each function
for r, M in ((1, 80), (2, 60), (3, 20)):
    pts = list(itertools.product([0, 1], repeat=r))
    first = {}
    for m in range(1, M + 1):
        for w in itertools.product(range(m), repeat=r):
            for th in range(m):
                f = tuple(int((sum(a * b for a, b in zip(w, x)) - th) % m == 0) for x in pts)
                if f not in first:
                    first[f] = m
    k = r + 2
    hb = (k ** 0.5 * r) ** k
    _detail_print(f'Lemma R MOD r={r}: {len(first)} distinct functions from moduli <= {M}; '
          f'largest minimal modulus needed = {max(first.values())}; proof bound ~{hb:.0f}')

if __name__ == "__main__":
    _out=_local_Path(__file__).resolve().parent/"results"/(_local_Path(__file__).stem+".details.txt")
    _out.write_text("\n".join(_detail_lines)+"\n")
    _builtins.print(_local_Path(__file__).name+": PASS; details="+_out.name)
