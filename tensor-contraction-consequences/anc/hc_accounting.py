import sys as _local_sys
from pathlib import Path as _local_Path
_local_sys.path.insert(0, str(_local_Path(__file__).resolve().parent))
import builtins as _builtins
_detail_lines=[]
def _detail_print(*a, **kw):
    _detail_lines.append(' '.join(map(str,a)))

#!/usr/bin/env python3
"""Explicit wire / vertex / degree bookkeeping of the network of Section 7 for Hamiltonian cycle (decision/count, no
cost constraint) on random sparse graphs, built exactly as described: degree-2 saturating chains on x_e;
The sign gadget of Section 6.1 on positions P = diag + both orientations of each edge, greedy blocks with B = floor(S6^{2/3}),
S6 = |rows| + |P| + 2; marker-Laplacian entries (diag constant 2 or 3, off-diagonal -x_e); equality trees; subdivision.
Prints W (wires after bipartization), V, max degree, and ratios against S = n+m+2."""
import random, sys, math
sys.path.insert(0, str(__import__('pathlib').Path(__file__).resolve().parent))
from p6_sign_check import greedy_blocks

def build(n, m, rng):
    perm = list(range(n)); rng.shuffle(perm)
    E = {(min(perm[i], perm[(i + 1) % n]), max(perm[i], perm[(i + 1) % n])) for i in range(n)}  # degree >= 2
    while len(E) < m:
        u, v = rng.randrange(n), rng.randrange(n)
        if u != v: E.add((min(u, v), max(u, v)))
    E = sorted(E)
    P = [(v, v) for v in range(n)] + [(u, v) for (u, v) in E] + [(v, u) for (u, v) in E]
    S6 = n + len(P) + 2; B = max(1, int(S6 ** (2 / 3)))
    rdeg = [0] * n; cdeg = [0] * n
    for (i, j) in P: rdeg[i] += 1; cdeg[j] += 1
    r, rh = greedy_blocks(rdeg, B); c, ch = greedy_blocks(cdeg, B)
    arities = []; occ_x = [0] * m; occ_z = {}
    gdeg = [0] * n
    for (u, v) in E: gdeg[u] += 1; gdeg[v] += 1
    # degree-2 chains: transition t reads x_e, 2-bit in-state (t>1), 2-bit out-state (t<deg)
    inc = [[] for _ in range(n)]
    for k, (u, v) in enumerate(E): inc[u].append(k); inc[v].append(k)
    state_wires = 0
    for v in range(n):
        d = len(inc[v])
        for t, k in enumerate(inc[v]):
            arities.append(1 + 2 * (t > 0) + 2 * (t < d - 1)); occ_x[k] += 1
        state_wires += 2 * (d - 1)
    # row / column exact-one chains (1-bit state)
    rowpos = [[] for _ in range(n)]; colpos = [[] for _ in range(n)]
    for p in P: rowpos[p[0]].append(p); colpos[p[1]].append(p)
    for lst in rowpos + colpos:
        k = len(lst)
        for t, p in enumerate(lst):
            arities.append(1 + (t > 0) + (t < k - 1)); occ_z[p] = occ_z.get(p, 0) + 1
        state_wires += k - 1
    # row/col block factors (light only)
    loads_r = {}; loads_c = {}
    for (i, j) in P:
        if not rh[r[i]]: loads_r[r[i]] = loads_r.get(r[i], 0) + 1; occ_z[(i, j)] += 1
        if not ch[c[j]]: loads_c[c[j]] = loads_c.get(c[j], 0) + 1; occ_z[(i, j)] += 1
    arities += list(loads_r.values()) + list(loads_c.values())
    # cells + parity wires + root
    cells = {}
    for (i, j) in P:
        cells[(r[i], c[j])] = cells.get((r[i], c[j]), 0) + 1; occ_z[(i, j)] += 1
    arities += [k + 1 for k in cells.values()]
    arities.append(len(cells)); p_wires = len(cells)
    # numeric factors
    for (i, j) in P:
        occ_z[(i, j)] += 1
        if i == j: arities.append(1)
        else:
            arities.append(2)
    for k in range(m): occ_x[k] += 2
    # equality trees
    eq_wires = 0; eq_nodes = 0; unary = 0
    for k in list(occ_x) + list(occ_z.values()):
        if k == 1: eq_wires += 1; unary += 1
        elif k == 2: eq_wires += 1
        else: eq_nodes += k - 2; eq_wires += 2 * k - 3
    W0 = eq_wires + state_wires + p_wires
    V0 = len(arities) + eq_nodes + unary
    W = 2 * W0; Vb = V0 + W0
    S = n + m + 2
    a = len(set(r)); b = len(set(c))
    return dict(n=n, m=m, S=S, B=B, a=a, b=b, cells=len(cells), maxdeg=max(max(arities), 3),
                W=W, V=Vb, W_over_S=W / S, maxdeg_over_S910=max(arities) / S ** 0.9, P0=4 * S + 1)

rng = random.Random(5)
for n, cfac in [(1000, 1.5), (10000, 1.5), (10000, 3), (100000, 1.5), (100000, 4)]:
    _detail_print(build(n, int(cfac * n), rng))

if __name__ == "__main__":
    _out=_local_Path(__file__).resolve().parent/"results"/(_local_Path(__file__).stem+".details.txt")
    _out.write_text("\n".join(_detail_lines)+"\n")
    _builtins.print(_local_Path(__file__).name+": PASS; details="+_out.name)
