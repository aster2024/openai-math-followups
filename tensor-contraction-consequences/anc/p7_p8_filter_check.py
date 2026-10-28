import sys as _local_sys
from pathlib import Path as _local_Path
_local_sys.path.insert(0, str(_local_Path(__file__).resolve().parent))
#!/usr/bin/env python3
"""Exhaustive small-case checks of the determinant filters and connectivity sums (Sections 6.2, 7, and 8).
All determinants are exact integers (fraction-free Gaussian elimination); all 'truth' values are
computed by brute force that does NOT use determinants."""
import itertools, random, sys
from fractions import Fraction
sys.path.insert(0, str(__import__('pathlib').Path(__file__).resolve().parent))
from p6_sign_check import det_int

def comps(vs, edges):
    par = {v: v for v in vs}
    def f(x):
        while par[x] != x:
            par[x] = par[par[x]]; x = par[x]
        return x
    for (u, v) in edges:
        par[f(u)] = f(v)
    groups = {}
    for v in vs:
        groups.setdefault(f(v), []).append(v)
    return list(groups.values())

def is_tree(vs, edges):
    return len(vs) >= 1 and len(edges) == len(vs) - 1 and len(comps(vs, edges)) == 1

def spanning_trees_brute(vs, edges):
    vs = list(vs)
    return sum(1 for T in itertools.combinations(edges, len(vs) - 1) if is_tree(vs, T)) if vs else 1

def A_undirected(n, U, F, M):
    A = [[0] * n for _ in range(n)]
    for (u, v) in F:
        A[u][v] -= 1; A[v][u] -= 1; A[u][u] += 1; A[v][v] += 1
    for v in range(n):
        A[v][v] += (v in M) + (v not in U)
    return A

def A_directed(n, U, F, M):
    A = [[0] * n for _ in range(n)]
    for (u, v) in F:
        A[u][v] -= 1; A[u][u] += 1
    for v in range(n):
        A[v][v] += (v in M) + (v not in U)
    return A

def rand_graph(rng, n, p):
    return [(u, v) for u in range(n) for v in range(u + 1, n) if rng.random() < p]

def deg(F, v):
    return sum(1 for e in F if v in e)

def subsets(lst):
    for k in range(len(lst) + 1):
        yield from itertools.combinations(lst, k)

def check_undirected(rng, n, E):
    global Eset; Eset = set(E)
    V = list(range(n)); res = {}
    # Marker-Laplacian identity per candidate: det A = tau(H+) (brute force spanning trees of H+)
    for _ in range(15):
        U = [v for v in V if rng.random() < 0.7]
        EU = [e for e in E if e[0] in U and e[1] in U]
        F = [e for e in EU if rng.random() < 0.6]
        Mk = [v for v in U if rng.random() < 0.3]
        rho = n
        Hp = list(F) + [(v, rho) for v in Mk]
        assert det_int(A_undirected(n, set(U), F, set(Mk))) == spanning_trees_brute(U + [rho], Hp)
    # HC: sum over 2-factors of det(M={r}) == n * #HC
    if n >= 3:
        r = 0
        Z = sum(det_int(A_undirected(n, set(V), F, {r})) for F in subsets(E) if all(deg(F, v) == 2 for v in V))
        hc = set()
        for perm in itertools.permutations(range(1, n)):
            cyc = (0,) + perm
            es = frozenset(tuple(sorted((cyc[i], cyc[(i + 1) % n]))) for i in range(n))
            if all(e in Eset for e in es):
                hc.add(es)
        assert Z == n * len(hc), (n, E, Z, len(hc)); res['HC'] = (Z, len(hc))
    # HP(s,t) and fixed-size simple s-t paths, M={s}
    if n >= 2:
        s, t = 0, n - 1
        for C in range(2, n + 1):
            Z = 0
            for U in itertools.combinations(V, C):
                if s not in U or t not in U: continue
                EU = [e for e in E if e[0] in U and e[1] in U]
                for F in subsets(EU):
                    if all(deg(F, v) == (1 if v in (s, t) else 2) for v in U):
                        Z += det_int(A_undirected(n, set(U), F, {s}))
            truth = 0
            for mid in itertools.permutations([v for v in V if v not in (s, t)], C - 2):
                path = (s,) + mid + (t,)
                if all(tuple(sorted((path[i], path[i + 1]))) in Eset for i in range(C - 1)):
                    truth += 1
            assert Z == truth, ('path', n, E, C, Z, truth)
    # Steiner trees containing terminal set T (r = min T), exact count of (U,F)
    T = sorted(rng.sample(V, rng.randint(1, min(3, n))))
    r = T[0]; Z = 0; truth = 0
    for U in subsets(V):
        if not set(T) <= set(U): continue
        EU = [e for e in E if e[0] in U and e[1] in U]
        for F in itertools.combinations(EU, len(U) - 1):
            Z += det_int(A_undirected(n, set(U), list(F), {r}))
            truth += is_tree(list(U), F)
    assert Z == truth, ('steiner', n, E, T, Z, truth); res['Steiner'] = Z
    # Steiner with T empty: all nonempty tree subgraphs via canonical root r=min U
    Z = 0; truth = 0
    for U in subsets(V):
        if not U: continue
        EU = [e for e in E if e[0] in U and e[1] in U]
        for F in itertools.combinations(EU, len(U) - 1):
            Z += det_int(A_undirected(n, set(U), list(F), {min(U)}))
            truth += is_tree(list(U), F)
    assert Z == truth
    # Connected vertex cover / connected dominating set with root r in U, F = E(G[U])
    for kind in ('cvc', 'cds'):
        for r in V:
            Z = 0; truth = 0; exists = False
            for U in subsets(V):
                if r not in U: continue
                Us = set(U)
                if kind == 'cvc' and not all(u in Us or v in Us for (u, v) in E): continue
                if kind == 'cds' and not all(v in Us or any((min(v, w), max(v, w)) in Eset and w in Us for w in V) for v in V): continue
                EU = [e for e in E if e[0] in Us and e[1] in Us]
                d = det_int(A_undirected(n, Us, EU, {r}))
                assert d >= 0
                conn = len(comps(list(U), EU)) == 1
                assert (d > 0) == conn
                if conn:
                    assert d == spanning_trees_brute(list(U), EU)
                    exists = True
                Z += d
            assert (Z > 0) == exists
    # FVS: (U,M), F=E(G[U]), |F|+|M|=|U|  ->  det in {0,1}, sum = sum_{forest U} prod comp sizes
    Z = 0; truth = 0; best_Z = {}; best_T = {}
    for U in subsets(V):
        Us = set(U); EU = [e for e in E if e[0] in Us and e[1] in Us]
        cs = comps(list(U), EU) if U else []
        forest = len(EU) == len(U) - len(cs)
        if forest:
            p = 1
            for c in cs: p *= len(c)
            truth += p
            best_T[n - len(U)] = best_T.get(n - len(U), 0) + p
        for Mk in subsets(list(U)):
            if len(EU) + len(Mk) != len(U): continue
            d = det_int(A_undirected(n, Us, EU, set(Mk)))
            assert d in (0, 1)
            Z += d; best_Z[n - len(U)] = best_Z.get(n - len(U), 0) + d
    assert Z == truth and {k: v for k, v in best_Z.items() if v} == best_T
    return res

def check_directed(rng, n, A):
    V = list(range(n)); Aset = set(A)
    # Directed filter per candidate: det = number of choice functions f:U->U+{rho} along F (or root arc for M) with all orbits reaching rho
    for _ in range(15):
        U = [v for v in V if rng.random() < 0.75]
        F = [a for a in A if a[0] in U and a[1] in U and rng.random() < 0.6]
        Mk = [v for v in U if rng.random() < 0.3]
        rho = -1
        opts = [[w for (x, w) in F if x == v] + ([rho] if v in Mk else []) for v in U]
        cnt = 0
        for choice in itertools.product(*opts):
            f = dict(zip(U, choice)); ok = True
            for v in U:
                seen = set(); x = v
                while x != rho and x not in seen:
                    seen.add(x); x = f[x]
                if x != rho: ok = False; break
            cnt += ok
        assert det_int(A_directed(n, set(U), F, set(Mk))) == cnt
    # directed HC count, M={r}: no division by n
    Z = 0
    for F in subsets(A):
        if all(sum(1 for a in F if a[0] == v) == 1 and sum(1 for a in F if a[1] == v) == 1 for v in V):
            Z += det_int(A_directed(n, set(V), list(F), {0}))
    truth = 0
    for perm in itertools.permutations(range(1, n)):
        cyc = (0,) + perm
        if n >= 2 and all((cyc[i], cyc[(i + 1) % n]) in Aset for i in range(n)):
            truth += 1
    assert Z == truth, ('dhc', n, A, Z, truth)
    # directed s->t simple paths with fixed vertex count, marker t
    s, t = 0, n - 1
    for C in range(2, n + 1):
        Z = 0
        for U in itertools.combinations(V, C):
            if s not in U or t not in U: continue
            AU = [a for a in A if a[0] in U and a[1] in U]
            for F in subsets(AU):
                outd = {v: sum(1 for a in F if a[0] == v) for v in U}
                ind = {v: sum(1 for a in F if a[1] == v) for v in U}
                want = {v: ((0, 1) if v == s else (1, 0) if v == t else (1, 1)) for v in U}
                if all((ind[v], outd[v]) == want[v] for v in U):
                    Z += det_int(A_directed(n, set(U), list(F), {t}))
        truth = 0
        for mid in itertools.permutations([v for v in V if v not in (s, t)], C - 2):
            path = (s,) + mid + (t,)
            if all((path[i], path[i + 1]) in Aset for i in range(C - 1)):
                truth += 1
        assert Z == truth, ('dpath', n, A, C, Z, truth)
    # MSCSS: det(F,{r}) * det(rev F,{r}) > 0 iff F strongly connected spanning
    r = 0
    for F in subsets(A):
        d1 = det_int(A_directed(n, set(V), list(F), {r}))
        d2 = det_int(A_directed(n, set(V), [(b, a) for (a, b) in F], {r}))
        def reach(arcs, src):
            seen = {src}; st = [src]
            while st:
                x = st.pop()
                for (a, b) in arcs:
                    if a == x and b not in seen: seen.add(b); st.append(b)
            return seen
        sc = len(reach(F, r)) == n and len(reach([(b, a) for (a, b) in F], r)) == n
        assert d1 >= 0 and d2 >= 0 and ((d1 * d2 > 0) == sc)

def check_metric_tsp(rng, n, E):
    """The route construction (Section 8) with T=V,R=empty: min over (mu in {0,1,2}^E, even degrees, support connected spanning) of cost
    == metric-closure TSP optimum (brute force), for connected G, n>=3."""
    V = list(range(n))
    if len(comps(V, E)) != 1 or n < 3: return None
    w = {e: rng.randint(0, 5) for e in E}
    INF = 10 ** 9
    d = [[0 if i == j else INF for j in V] for i in V]
    for (u, v) in E:
        d[u][v] = d[v][u] = min(d[u][v], w[(u, v)])
    for k in V:
        for i in V:
            for j in V:
                d[i][j] = min(d[i][j], d[i][k] + d[k][j])
    tsp = min(sum(d[c[i]][c[(i + 1) % n]] for i in range(n)) for c in ((0,) + p for p in itertools.permutations(range(1, n))))
    best = INF
    for mu in itertools.product((0, 1, 2), repeat=len(E)):
        if any(sum(m for e, m in zip(E, mu) if v in e) % 2 for v in V): continue
        F = [e for e, m in zip(E, mu) if m]
        if det_int(A_undirected(n, set(V), F, {0})) == 0: continue
        best = min(best, sum(w[e] * m for e, m in zip(E, mu)))
    assert best == tsp, (E, w, best, tsp)
    return best

if __name__ == "__main__":
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    rng = random.Random(seed)
    cnt = {'und': 0, 'dir': 0, 'tsp': 0, 'hc_pos': 0}
    for trial in range(60):
        n = rng.randint(3, 6)
        E = rand_graph(rng, n, rng.choice([0.5, 0.7, 0.9]))
        Eset = set(E)
        res = check_undirected(rng, n, E); cnt['und'] += 1
        cnt['hc_pos'] += res.get('HC', (0, 0))[1] > 0
        if len(E) <= 8 and check_metric_tsp(rng, n, E) is not None: cnt['tsp'] += 1
    for trial in range(40):
        n = rng.randint(2, 5)
        A = [(u, v) for u in range(n) for v in range(n) if u != v and rng.random() < 0.55]
        if len(A) <= 12:
            check_directed(rng, n, A); cnt['dir'] += 1
    print(f"seed={seed}: undirected graphs {cnt['und']} (with >=1 HC: {cnt['hc_pos']}), "
          f"directed graphs {cnt['dir']}, metric-TSP graphs {cnt['tsp']}; ALL PASS")
