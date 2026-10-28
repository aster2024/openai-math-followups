import os as _os
for _name in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'):
    _os.environ[_name]='1'
"""Exhaustive factor-contraction check of sliced gadgets (Section 4.1).

Unlike check_gadgets.py (arithmetic replay only), this builds the 0/1 factors
of the sliced gadget explicitly -- slicing chains
F_{k,i}, carry factors G_k (two chains + hidden quotient q for MOD), final
factor -- with every multi-bit wire given its FULL domain 2^{bits} (so invalid
codewords are included), and contracts the network exactly (einsum over all
internal wire values).  For each input-port assignment it checks:
  * consistent copies:  #extensions(y) == [y == f(x)]   (unique extension + function)
  * inconsistent copies (each slice k reads its own copy of x): sum_y #ext == 1
Bit widths follow Section 4.1: mu = L+ceil(log2(r+1)), gamma = ceil(log2(r+3))
(offset code, value = code-1), q has ceil(log2(r+1)) bits, codes q>r give 0,
K = ceil(B/L), K* = ceil((B+ceil(log2(r+2)))/L).  Block size `blk` plays b.
Splitting the MOD carry factor G_k into one factor per chain (both reading q)
does not change the contraction (product of the two = the joint factor).
Run: nice -n 19 python3 -I check_G1_tensor.py     (runtime recorded by the serial runner)
"""
import itertools, random, sys
import numpy as np
def _integer_zeros(shape):
    return np.zeros(shape, dtype=np.int64)


random.seed(1028)
MUT = sys.argv[1] if len(sys.argv) > 1 else ''  # mutation tests: nod2 / noqcheck / gamma-1
LETTERS = 'abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ'


def clog2(v):  # ceil(log2 v) for v >= 1
    return (v - 1).bit_length()


def contract(factors, doms, free):
    """factors: list of (vars, ndarray). Exact sum over all non-free vars."""
    names = {}
    for vs, _ in factors:
        for v in vs:
            if v not in names:
                names[v] = LETTERS[len(names)]
    for v in free:
        if v not in names:
            names[v] = LETTERS[len(names)]
    assert len(names) <= len(LETTERS)
    spec = ','.join(''.join(names[v] for v in vs) for vs, _ in factors)
    spec += '->' + ''.join(names[v] for v in free)
    return np.einsum(spec, *[a for _, a in factors], optimize='greedy')


def build_and_count(kind, w, theta, m, xcopies, L, blk):
    """xcopies[k] = input-port assignment read by slice chain k. Returns counts over y."""
    r = len(w)
    if kind == 'MOD':
        u = [wj % m for wj in w]
        B = max(1, (m - 1).bit_length())
        lit = [list(xc) for xc in xcopies]
    else:
        u = [abs(wj) for wj in w]
        B = max(1, max(uj.bit_length() for uj in u))
        lit = [[xj if wj >= 0 else 1 - xj for wj, xj in zip(w, xc)] for xc in xcopies]
    K = -(-B // L)
    Ks = -(-(B + clog2(r + 2)) // L)
    mu = L + clog2(r + 1)
    gam = clog2(r + 3) - (1 if MUT == 'gamma-1' else 0)
    qb = clog2(r + 1)
    blocks = [list(range(i, min(i + blk, r))) for i in range(0, r, blk)]
    t = len(blocks)
    D = {}
    factors = []
    # slicing chains
    for k in range(K):
        uk = [(uj >> (k * L)) & ((1 << L) - 1) for uj in u]
        for i, bl in enumerate(blocks):
            add = sum(uk[j] * lit[k][j] for j in bl)
            out = ('P', k, i)
            D[out] = 1 << mu
            if i == 0:
                a = _integer_zeros(1 << mu)
                if add < (1 << mu):
                    a[add] = 1
                factors.append(([out], a))
            else:
                inp = ('P', k, i - 1)
                a = _integer_zeros((1 << mu, 1 << mu))
                for pv in range(1 << mu):
                    if pv + add < (1 << mu):
                        a[pv, pv + add] = 1
                factors.append(([inp, out], a))
    # constants
    if kind == 'THR' or kind == 'ETHR':
        T = theta + sum(abs(wj) for wj in w if wj < 0)
        if T < 0:
            T = 0 if kind == 'THR' else r * (1 << B)
        if T > r * (1 << B):
            T = r * (1 << B)
        chains = [(0, lambda q: T)]
    else:
        th = theta % m
        A = m - th
        chains = [(A, lambda q: q * m), (A, lambda q: (q + 1) * m)]
    assert all(c[0] < (1 << (Ks * L)) for c in chains)
    dig = lambda v, k: (v >> (k * L)) & ((1 << L) - 1)
    ncodes = 1 << gam
    for ch, (A, Tf) in enumerate(chains):
        for k in range(Ks):
            vs, shape = [], []
            hasY = k < K
            if hasY:
                vs.append(('P', k, t - 1)); shape.append(1 << mu)
            if k > 0:
                vs += [('c', ch, k - 1), ('e', ch, k - 1)]; shape += [ncodes, 2]
            if kind == 'MOD':
                vs.append('q'); shape.append(1 << qb)
            vs += [('c', ch, k), ('e', ch, k)]; shape += [ncodes, 2]
            for v, s in zip(vs, shape):
                D[v] = s
            a = _integer_zeros(shape)
            ranges = []
            ranges.append(range(1 << mu) if hasY else [0])
            ranges.append(range(ncodes) if k > 0 else [1])   # c_{-1}=0 -> code 1
            ranges.append(range(2) if k > 0 else [1])        # e_{-1}=1
            ranges.append(range(1 << qb) if kind == 'MOD' else [0])
            for Y, cc, ee, q in itertools.product(*ranges):
                if kind == 'MOD' and q > r and MUT != 'noqcheck':
                    continue  # invalid q codeword -> entry 0
                Tp = Tf(q)
                Tp = Tp & ((1 << (Ks * L)) - 1)  # only digits 0..K*-1 are ever used
                z = Y + dig(A, k) - dig(Tp, k) + (cc - 1)
                cn = z >> L
                en = int(ee == 1 and (z & ((1 << L) - 1)) == 0)
                code = cn + 1
                if not (0 <= code < ncodes):
                    continue  # carry out of representable range -> entry 0
                idx = []
                if hasY: idx.append(Y)
                if k > 0: idx += [cc, ee]
                if kind == 'MOD': idx.append(q)
                idx += [code, en]
                a[tuple(idx)] = 1
            factors.append((vs, a))
    # final factor
    D['y'] = 2
    last = Ks - 1
    if kind == 'MOD':
        vs = [('c', 0, last), ('e', 0, last), ('c', 1, last), 'y']
        a = _integer_zeros((ncodes, 2, ncodes, 2))
        for c1, e1, c2 in itertools.product(range(ncodes), range(2), range(ncodes)):
            if c1 - 1 >= 0 and (c2 - 1 < 0 or MUT == 'nod2'):
                a[c1, e1, c2, int(c1 - 1 == 0 and e1 == 1)] = 1
    else:
        vs = [('c', 0, last), ('e', 0, last), 'y']
        a = _integer_zeros((ncodes, 2, 2))
        for c1, e1 in itertools.product(range(ncodes), range(2)):
            yv = int(c1 - 1 >= 0) if kind == 'THR' else int(c1 - 1 == 0 and e1 == 1)
            a[c1, e1, yv] = 1
    factors.append((vs, a))
    for v in vs:
        D[v] = a.shape[vs.index(v)]
    # every variable must be touched by >=1 factor; sum over all non-y vars
    cnt = contract(factors, D, ['y'])
    nbits = sum((int(D[v]).bit_length() - 1) for v in D if v != 'y')
    return cnt, nbits


def direct(kind, w, theta, m, x):
    s = sum(wj * xj for wj, xj in zip(w, x))
    if kind == 'THR':
        return int(s >= theta)
    if kind == 'ETHR':
        return int(s == theta)
    return int((s - theta) % m == 0)


stats = {'THR': 0, 'ETHR': 0, 'MOD': 0}
incons = 0
maxbits = 0
for trial in range(260):
    kind = ['THR', 'ETHR', 'MOD'][trial % 3]
    r = random.choice([2, 3, 4, 5])
    L = random.choice([1, 2])
    blk = random.choice([1, 2, 3])
    Bw = random.randint(1, 4)
    w = [random.randint(-(1 << Bw) + 1, (1 << Bw) - 1) for _ in range(r)]
    m = random.randint(1, 1 << Bw)
    if kind == 'ETHR' and random.random() < 0.6:
        x0 = [random.randint(0, 1) for _ in range(r)]
        theta = sum(a * b for a, b in zip(w, x0))
    else:
        theta = random.randint(-(r + 2) << Bw, (r + 2) << Bw)
    if kind == 'MOD':
        B = max(1, (m - 1).bit_length())
    else:
        B = max(1, max(abs(a).bit_length() for a in w))
    K = -(-B // L)
    for x in itertools.product([0, 1], repeat=r):
        cnt, nb = build_and_count(kind, w, theta, m, [x] * K, L, blk)
        maxbits = max(maxbits, nb)
        f = direct(kind, w, theta, m, x)
        exp = np.array([1 - f, f], dtype=np.int64)
        assert np.array_equal(cnt, exp), (kind, w, theta, m, x, L, blk, cnt)
        stats[kind] += 1
    # inconsistent copies: unique extension only
    if K >= 2:
        for _ in range(3):
            xc = [tuple(random.randint(0, 1) for _ in range(r)) for _ in range(K)]
            cnt, nb = build_and_count(kind, w, theta, m, xc, L, blk)
            assert cnt.sum() == 1, (kind, w, theta, m, xc, cnt)
            incons += 1
print('Sliced-gadget tensor checks: PASS; consistent', stats, '; independently assigned slice copies', incons, '; max internal bits', maxbits, '; integer tensors=int64')
