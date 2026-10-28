import sys as _local_sys
from pathlib import Path as _local_Path
_local_sys.path.insert(0, str(_local_Path(__file__).resolve().parent))
import builtins as _builtins
_detail_lines=[]
def _detail_print(*a, **kw):
    _detail_lines.append(' '.join(map(str,a)))

#!/usr/bin/env python3
"""End-to-end mini check of the Hamiltonian-cycle construction (Section 7) on tiny graphs: outer sum over edge bits x with the
local degree-2 system, inner sign factor network (all z in {0,1}^E, greedy blocks with tiny B) carrying
the marker-Laplacian entries A(x) with marker r=0; total Z is reduced mod 2^{P0}, P0=4S+1, read back as least
non-negative residue and divided by n.  Compared with brute-force #HC."""
import itertools, sys
sys.path.insert(0, str(__import__('pathlib').Path(__file__).resolve().parent))
from p6_sign_check import network_value, greedy_blocks

def hc_count(n, E):
    Es = set(E); hc = set()
    for perm in itertools.permutations(range(1, n)):
        cyc = (0,) + perm
        es = frozenset(tuple(sorted((cyc[i], cyc[(i + 1) % n]))) for i in range(n))
        if all(e in Es for e in es): hc.add(es)
    return len(hc)

def run(n, E, B):
    pos = sorted({(v, v) for v in range(n)} | {(u, v) for (u, v) in E} | {(v, u) for (u, v) in E})
    rdeg = [sum(1 for (i, j) in pos if i == x) for x in range(n)]
    cdeg = [sum(1 for (i, j) in pos if j == x) for x in range(n)]
    r, rh = greedy_blocks(rdeg, B); c, ch = greedy_blocks(cdeg, B)
    S = n + len(E) + 2; P0 = 4 * S + 1; mod = 1 << P0
    Z = 0
    for xs in itertools.product((0, 1), repeat=len(E)):
        F = [e for e, b in zip(E, xs) if b]
        if any(sum(1 for e in F if v in e) != 2 for v in range(n)): continue
        A = [[0] * n for _ in range(n)]
        for (u, v) in F:
            A[u][v] = A[v][u] = -1
        for v in range(n):
            A[v][v] = 2 + (v == 0)
        Z = (Z + network_value(pos, n, A, r, c, rh, ch, False)) % mod
    assert Z % n == 0
    return Z // n, hc_count(n, E), len(set(r)), len(set(c))

K4 = [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]
cycle5 = [(0,1),(1,2),(2,3),(3,4),(0,4)]
chorded_cycle5 = cycle5 + [(1,3)]
TT = [(0,1),(1,2),(2,0),(3,4),(4,5),(5,3)]
for (n, E, B) in [(4, K4, 2), (4, K4, 8), (5, cycle5, 2), (5, cycle5, 6), (5, chorded_cycle5, 3), (5, chorded_cycle5, 7),
                  (6, TT, 2), (6, TT, 6), (6, TT, 9)]:
    got, truth, a, b = run(n, E, B)
    assert got == truth, (n, E, got, truth)
    _detail_print(f"n={n} m={len(E)} B={B} row-blocks={a} col-blocks={b}: network readback #HC={got}, brute force={truth}")
_detail_print("ALL PASS")

if __name__ == "__main__":
    _out=_local_Path(__file__).resolve().parent/"results"/(_local_Path(__file__).stem+".details.txt")
    _out.write_text("\n".join(_detail_lines)+"\n")
    _builtins.print(_local_Path(__file__).name+": PASS; details="+_out.name)
