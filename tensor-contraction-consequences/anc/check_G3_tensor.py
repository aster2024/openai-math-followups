import os as _os
for _name in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'):
    _os.environ[_name]='1'
"""Exhaustive factor-contraction check of residue chains (Section 4.3, hashed ETHR/MOD).

Builds the residue chain literally: block factors read their block inputs and
P_{i-1} (pi bits, full domain 2^pi, codes >= p give entry 0), output P_i;
the final factor reads P_t and y and checks y = [P_t in T mod p].  pi is the
bit length of the LARGEST prime in the family (graph independent of p).
Contracts exactly and checks #ext(y) == [y == f_{v,p}(x)] for every x, and
that f_{v,p} >= f_v (one-sided).  Also tallies the bad-prime fraction against
N_v-style bound |T| * bitlen.
Run: nice -n 19 python3 -I check_G3_tensor.py   (runtime recorded by the serial runner)
"""
import itertools, random
import numpy as np
def _integer_zeros(shape):
    return np.zeros(shape, dtype=np.int64)


random.seed(2810)


def primes_above(lo, cnt):
    out, v = [], lo + 1
    while len(out) < cnt:
        if all(v % d for d in range(2, int(v ** 0.5) + 1)):
            out.append(v)
        v += 1
    return out


FAM = primes_above(6, 24)          # family: first 24 primes > S=6
PI = max(FAM).bit_length()          # common wire width


def gadget_counts(kind, w, theta, m, x, p, blk):
    r = len(w)
    if kind == 'ETHR':
        wt = list(w); T = {theta}
    else:
        wt = [a % m for a in w]; th = theta % m; T = {th + q * m for q in range(r)}
    Tp = {t % p for t in T}
    blocks = [list(range(i, min(i + blk, r))) for i in range(0, r, blk)]
    N = 1 << PI
    vec = None  # vector over P values (full domain)
    for i, bl in enumerate(blocks):
        add = sum((wt[j] % p) * x[j] for j in bl)
        M = _integer_zeros((N, N))
        for pv in range(N):
            if pv < p:                       # out-of-range input code -> entry 0
                M[pv, (pv + add) % p] = 1
        if i == 0:
            v0 = _integer_zeros(N); v0[add % p] = 1
            vec = v0
        else:
            vec = vec @ M
    fin = _integer_zeros((N, 2))
    for pv in range(N):
        if pv < p:
            fin[pv, int(pv in Tp)] = 1
    return vec @ fin


def direct(kind, w, theta, m, x):
    s = sum(a * b for a, b in zip(w, x))
    return int(s == theta) if kind == 'ETHR' else int((s - theta) % m == 0)


cases = 0
for trial in range(400):
    kind = random.choice(['ETHR', 'MOD'])
    r = random.randint(2, 5)
    blk = random.randint(1, 3)
    Bw = random.randint(3, 12)
    w = [random.randint(-(1 << Bw), 1 << Bw) for _ in range(r)]
    m = random.randint(2, 1 << Bw)
    theta = random.randint(-(1 << Bw), 1 << Bw)
    if kind == 'ETHR' and random.random() < 0.5:
        theta = sum(a * b for a, b in zip(w, [random.randint(0, 1) for _ in range(r)]))
    for x in itertools.product([0, 1], repeat=r):
        f = direct(kind, w, theta, m, x)
        bad = 0
        for p in FAM:
            cnt = gadget_counts(kind, w, theta, m, x, p, blk)
            assert cnt.sum() == 1, (kind, w, theta, m, x, p, cnt)   # unique extension
            fp = int(cnt[1] == 1)
            assert fp >= f                                          # one-sided
            if kind == 'ETHR':
                s = sum(a * b for a, b in zip(w, x)); T = [theta]
            else:
                s = sum((a % m) * b for a, b in zip(w, x)); T = [theta % m + q * m for q in range(r)]
            assert fp == int(any((s - t) % p == 0 for t in T))       # = [Sigma mod p in T mod p]
            bad += fp != f
            cases += 1
        if f == 0:
            s = sum(a * b for a, b in zip(w, x)) if kind == 'ETHR' else sum((a % m) * b for a, b in zip(w, x))
            T = [theta] if kind == 'ETHR' else [theta % m + q * m for q in range(r)]
            bits = max(abs(s - t).bit_length() for t in T)
            assert bad <= len(T) * bits
print('Residue-chain tensor checks passed:', cases, '(gadget, x, p) triples; family', len(FAM),
      'primes, wire width', PI, '; integer tensors=int64')
