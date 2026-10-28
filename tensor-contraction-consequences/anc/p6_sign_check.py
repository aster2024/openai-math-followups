import sys as _local_sys
from pathlib import Path as _local_Path
_local_sys.path.insert(0, str(_local_Path(__file__).resolve().parent))
#!/usr/bin/env python3
"""Independent exhaustive check of the sparse-permutation sign decomposition (Section 6.1).

(1) Integer identity inv(sigma) = I_R + I_C + I_x + sum I_uv for every permutation supported on E,
    with the order-preserving greedy light/heavy blocking in Section 6.1 (block budget B, deliberately tiny so
    that heavy rows/cols and multi-row blocks both occur).
(2) Contraction of the sign factor system (row/col exact-one, row-block, col-block, cell(+parity wire),
    root quadratic form, numeric entries) summed over ALL z in {0,1}^E (and, for small cases, over all
    parity-wire values p) equals det(A) exactly, for random integer A supported on E.
"""
import itertools, random, sys
from fractions import Fraction

def det_int(M):
    n = len(M)
    if n == 0:
        return 1
    A = [[Fraction(x) for x in row] for row in M]
    d = Fraction(1)
    for c in range(n):
        piv = None
        for r in range(c, n):
            if A[r][c] != 0:
                piv = r; break
        if piv is None:
            return 0
        if piv != c:
            A[c], A[piv] = A[piv], A[c]; d = -d
        d *= A[c][c]
        for r in range(c + 1, n):
            f = A[r][c] / A[c][c]
            if f:
                for k in range(c, n):
                    A[r][k] -= f * A[c][k]
    assert d.denominator == 1
    return int(d)

def greedy_blocks(deg, B):
    """order-preserving greedy blocks; heavy (deg>B) indices are singleton blocks"""
    lab = [None] * len(deg); heavy = []
    cur = -1; load = None
    for i, d in enumerate(deg):
        if d > B:
            cur += 1; lab[i] = cur; heavy.append(True); load = None
        else:
            if load is None or load + d > B:
                cur += 1; heavy.append(False); load = 0
            lab[i] = cur; load += d
    return lab, heavy

def inv(sig):
    n = len(sig)
    return sum(1 for i in range(n) for j in range(i + 1, n) if sig[i] > sig[j])

def perms_on(E, N):
    rows = [[j for (i, j) in E if i == r] for r in range(N)]
    def rec(i, used, acc):
        if i == N:
            yield tuple(acc); return
        for j in rows[i]:
            if j not in used:
                used.add(j); acc.append(j)
                yield from rec(i + 1, used, acc)
                acc.pop(); used.discard(j)
    yield from rec(0, set(), [])

def decomposition(sig, r, c):
    N = len(sig)
    sinv = [None] * N
    for i, j in enumerate(sig):
        sinv[j] = i
    IR = sum(1 for i in range(N) for k in range(i + 1, N) if r[i] == r[k] and c[sig[i]] > c[sig[k]])
    IC = sum(1 for j in range(N) for k in range(j + 1, N) if c[j] == c[k] and r[sinv[j]] > r[sinv[k]])
    Iuv = sum(1 for i in range(N) for k in range(i + 1, N)
              if r[i] == r[k] and c[sig[i]] == c[sig[k]] and sig[i] > sig[k])
    a = max(r) + 1; b = max(c) + 1
    n = [[0] * b for _ in range(a)]
    for i in range(N):
        n[r[i]][c[sig[i]]] += 1
    Ix = sum(n[u][v] * n[u2][v2] for u in range(a) for v in range(b)
             for u2 in range(u + 1, a) for v2 in range(v))
    return IR, IC, Iuv, Ix

def network_value(E, N, A, r, c, rheavy, cheavy, full_p):
    a = max(r) + 1; b = max(c) + 1
    cells = {}
    for (i, j) in E:
        cells.setdefault((r[i], c[j]), []).append((i, j))
    cell_keys = sorted(cells)
    total = 0
    Elist = list(E)
    for mask in range(1 << len(Elist)):
        sel = [Elist[t] for t in range(len(Elist)) if mask >> t & 1]
        # row / column exact-one chains
        rc = [0] * N; cc = [0] * N
        for (i, j) in sel:
            rc[i] += 1; cc[j] += 1
        if any(x != 1 for x in rc) or any(x != 1 for x in cc):
            continue  # chains give 0 (unique-extension chains, value 0 on illegal z)
        sig = [None] * N
        for (i, j) in sel:
            sig[i] = j
        sinv = [None] * N
        for i, j in enumerate(sig):
            sinv[j] = i
        val = 1
        # numeric factors
        for (i, j) in sel:
            val *= A[i][j]
        # row-block factors (light only; read only positions of their own rows)
        for u in range(a):
            if rheavy[u]:
                continue
            rows_u = [i for i in range(N) if r[i] == u]
            cnt = 0
            for x in range(len(rows_u)):
                for y in range(x + 1, len(rows_u)):
                    if c[sig[rows_u[x]]] > c[sig[rows_u[y]]]:
                        cnt += 1
            val *= (-1) ** cnt
        for v in range(b):
            if cheavy[v]:
                continue
            cols_v = [j for j in range(N) if c[j] == v]
            cnt = 0
            for x in range(len(cols_v)):
                for y in range(x + 1, len(cols_v)):
                    if r[sinv[cols_v[x]]] > r[sinv[cols_v[y]]]:
                        cnt += 1
            val *= (-1) ** cnt
        # cell factors with parity wires p_uv, and root quadratic form
        def cell_sign(key):
            s = [(i, j) for (i, j) in cells[key] if (i, j) in selset]
            rows_s = [i for i, _ in s]; cols_s = [j for _, j in s]
            if len(set(rows_s)) < len(rows_s) or len(set(cols_s)) < len(cols_s):
                return 0, None
            s.sort()
            cnt = sum(1 for x in range(len(s)) for y in range(x + 1, len(s)) if s[x][1] > s[y][1])
            return (-1) ** cnt, len(s) % 2
        selset = set(sel)
        info = {k: cell_sign(k) for k in cell_keys}
        def root(p):
            q = 0
            for (u, v), pv in p.items():
                if not pv:
                    continue
                for (u2, v2), pv2 in p.items():
                    if pv2 and u2 > u and v2 < v:
                        q += 1
            return (-1) ** q
        if full_p:
            acc = 0
            for bits in itertools.product((0, 1), repeat=len(cell_keys)):
                p = dict(zip(cell_keys, bits))
                term = 1
                for k in cell_keys:
                    sgn, par = info[k]
                    if sgn == 0 or par != p[k]:
                        term = 0; break
                    term *= sgn
                if term:
                    acc += term * root(p)
            total += val * acc
        else:
            term = 1; p = {}
            for k in cell_keys:
                sgn, par = info[k]
                term *= sgn; p[k] = par
            total += val * term * root(p)
    return total

def main(seed=1, trials=400):
    rng = random.Random(seed)
    n_id = 0; n_net = 0; n_full = 0; heavy_seen = 0; multi_seen = 0
    for t in range(trials):
        N = rng.randint(1, 6)
        dens = rng.choice([0.25, 0.4, 0.6, 0.9])
        E = set((i, j) for i in range(N) for j in range(N) if rng.random() < dens)
        if rng.random() < 0.5:
            E |= {(i, i) for i in range(N)}           # Laplacian-like diagonal
        if rng.random() < 0.3 and N > 1:             # force a heavy row and a heavy column
            h = rng.randrange(N); E |= {(h, j) for j in range(N)}; E |= {(j, h) for j in range(N)}
        E = sorted(E)
        rdeg = [sum(1 for (i, j) in E if i == x) for x in range(N)]
        cdeg = [sum(1 for (i, j) in E if j == x) for x in range(N)]
        if min(rdeg) == 0 or min(cdeg) == 0:
            continue  # The construction outputs the zero scalar network directly
        B = rng.choice([1, 2, 3, 4, 5])
        r, rheavy = greedy_blocks(rdeg, B)
        c, cheavy = greedy_blocks(cdeg, B)
        heavy_seen += any(rheavy) or any(cheavy)
        multi_seen += any(r.count(u) > 1 for u in set(r))
        # (1) integer identity
        for sig in perms_on(E, N):
            IR, IC, Iuv, Ix = decomposition(sig, r, c)
            assert inv(sig) == IR + IC + Iuv + Ix, (E, sig, r, c)
            n_id += 1
        # (2) network contraction == det A
        if len(E) <= 14:
            A = [[0] * N for _ in range(N)]
            for (i, j) in E:
                A[i][j] = rng.randint(-3, 3)
            ncells = len({(r[i], c[j]) for (i, j) in E})
            full = len(E) <= 10 and ncells <= 6
            Z = network_value(E, N, A, r, c, rheavy, cheavy, full)
            D = det_int(A)
            assert Z == D, (E, A, Z, D)
            n_net += 1; n_full += full
    print(f"seed={seed}: identity checked on {n_id} (E,sigma) pairs; network==det on {n_net} instances "
          f"({n_full} with explicit sum over all parity wires); instances with heavy block {heavy_seen}, "
          f"with multi-row block {multi_seen}; ALL PASS")

if __name__ == "__main__":
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 1, int(sys.argv[2]) if len(sys.argv) > 2 else 400)
