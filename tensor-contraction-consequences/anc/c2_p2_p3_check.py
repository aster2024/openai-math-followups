import sys as _local_sys
from pathlib import Path as _local_Path
_local_sys.path.insert(0, str(_local_Path(__file__).resolve().parent))
import builtins as _builtins
_detail_lines=[]
def _detail_print(*a, **kw):
    _detail_lines.append(' '.join(map(str,a)))

#!/usr/bin/env python3
"""Brute-force check of consistent cuts (consistent cuts with fixed root = 2^{cc-1}; Hamiltonian identity mod 2)
and marked consistent cuts (marked consistent cuts odd  <=>  G[U] forest with one marker per component, given e(U)=|U|-|M|).
These checks accompany the Cut&Count discussion in Section 9.2."""
import itertools, random, sys
sys.path.insert(0, str(__import__('pathlib').Path(__file__).resolve().parent))
from p7_p8_filter_check import comps, subsets, rand_graph
rng = random.Random(11); factor_cases = marker_cases = 0
for trial in range(80):
    n = rng.randint(3, 6); E = rand_graph(rng, n, rng.choice([0.5, 0.8])); V = list(range(n))
    # Consistent-cut polynomial identity, evaluated as a dict weight->count, with random weights
    w = {e: rng.randint(0, 3) for e in E}
    lhs = {}
    for F in subsets(E):
        if any(sum(1 for e in F if v in e) != 2 for v in V): continue
        cuts = sum(1 for col in itertools.product((0, 1), repeat=n) if col[0] == 0 and all(col[u] == col[v] for (u, v) in F))
        assert cuts == 2 ** (len(comps(V, F)) - 1)
        W = sum(w[e] for e in F); lhs[W] = lhs.get(W, 0) + cuts
        factor_cases += 1
    hc = {}
    for perm in itertools.permutations(range(1, n)):
        cyc = (0,) + perm
        es = frozenset(tuple(sorted((cyc[i], cyc[(i + 1) % n]))) for i in range(n))
        if all(e in set(E) for e in es): hc[es] = sum(w[e] for e in es)
    hcW = {}
    for es, W in hc.items(): hcW[W] = hcW.get(W, 0) + 1
    assert {k: v % 2 for k, v in lhs.items() if v % 2} == {k: v % 2 for k, v in hcW.items() if v % 2}
    # Marked consistent cuts
    for U in subsets(V):
        Us = set(U); EU = [e for e in E if e[0] in Us and e[1] in Us]
        for Mk in subsets(list(U)):
            cuts = sum(1 for col in itertools.product((0, 1), repeat=n)
                       if all(col[v] == 0 for v in Mk) and all(col[v] == 0 for v in V if v not in Us)
                       and all(col[a] == col[b] for (a, b) in EU))
            cs = comps(list(U), EU) if U else []
            z = sum(1 for c in cs if not set(c) & set(Mk))
            assert cuts == 2 ** z
            if len(EU) == len(U) - len(Mk):
                good = len(EU) == len(U) - len(cs) and all(len(set(c) & set(Mk)) == 1 for c in cs)
                assert (cuts % 2 == 1) == good
                marker_cases += 1
_detail_print(f"Consistent cuts checked on {factor_cases} 2-factors (incl. mod-2 weight generating function), marked cuts on {marker_cases} (U,M) pairs; ALL PASS")

if __name__ == "__main__":
    _out=_local_Path(__file__).resolve().parent/"results"/(_local_Path(__file__).stem+".details.txt")
    _out.write_text("\n".join(_detail_lines)+"\n")
    _builtins.print(_local_Path(__file__).name+": PASS; details="+_out.name)
