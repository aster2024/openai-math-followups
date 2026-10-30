"""Exact modular check, split by partial-matching support index.

Reference counts enumerate degree-two edge sets and supported permutations.
Möbius coefficients are computed directly by the subset definition, without
a Gauss-sum optimization.  Every queried CNF is counted by check_cnf_reference's
independent bitset counter.  Shards have exact ranges and additive residues.
"""
import argparse
from collections import Counter
from itertools import combinations
import json
import os
from pathlib import Path
import resource
import sys
import time
sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_cnf_reference import exact_count, reference_graph
from cnf_circuits import determinant_hc_cnf


def instance(case):
    if case == "k6":
        return 6, list(combinations(range(6), 2))
    if case == "k33":
        return 6, [(i,j) for i in range(3) for j in range(3,6)]
    if case in ("c8", "c9"):
        n = int(case[1:])
        return n, [(i,(i+1)%n) for i in range(n)]
    if case in ("wheel7", "wheel8"):
        n = int(case[-1])
        return n, [(0,v) for v in range(1,n)] + [(v,1+v%(n-1)) for v in range(1,n)]
    if case == "three_triangles":
        return 9, [(3*k+i,3*k+j) for k in range(3) for i,j in combinations(range(3),2)]
    if case == "triangles_bridge":
        return 6, [(0,1),(0,2),(1,2),(3,4),(3,5),(4,5),(2,3)]
    raise ValueError(case)


def sign(positions):
    inversions = sum((a<c and b>d) or (c<a and d>b)
                     for (a,b),(c,d) in combinations(positions,2))
    return (-1)**((sum(a!=b for a,b in positions)+inversions)%2)


def coefficient(selected):
    s = len(selected)
    result = 0
    for mask in range(1 << s):
        subset = [p for i,p in enumerate(selected) if mask >> i & 1]
        result += (-1)**((s-mask.bit_count())%2) * sign(subset)
    return result


def inventory(n, edges, positions):
    """Weighted unsigned permutation selections, independently enumerated."""
    cuts, hc, factors = reference_graph(n, edges, [1]*len(edges))
    index = {p:i for i,p in enumerate(positions)}
    counts = Counter()
    for chosen in factors:
        allowed = [{i} for i in range(n)]
        for e in chosen:
            u,v = edges[e]
            allowed[u].add(v)
            allowed[v].add(u)
        def walk(row, used, bits, weight):
            if row == n:
                counts[bits] += weight
                return
            for col in sorted(allowed[row]):
                if used >> col & 1:
                    continue
                multiplier = (3 if row == 0 else 2) if row == col else 1
                walk(row+1, used | 1<<col, bits | 1<<index[row,col], weight*multiplier)
        walk(0,0,0,1)
    signed = sum(weight*sign([p for i,p in enumerate(positions) if bits>>i&1])
                 for bits,weight in counts.items())
    expected_hc = sum(hc.values())
    assert signed == n*expected_hc
    return counts, expected_hc, len(factors), signed


def matching_supports(n, positions, degree):
    rows = [[] for _ in range(n)]
    for i,(u,v) in enumerate(positions):
        rows[u].append((i,v))
    def walk(row, columns, selected):
        if row == n:
            yield tuple(selected)
            return
        yield from walk(row+1,columns,selected)
        if len(selected) < degree:
            for i,col in rows[row]:
                if columns>>col&1 == 0:
                    yield from walk(row+1, columns | 1<<col, selected+[i])
    return list(walk(0,0,[]))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--case", required=True)
    ap.add_argument("--bits", type=int, default=4)
    ap.add_argument("--start", type=int, default=0)
    ap.add_argument("--stop", type=int, default=1000)
    ap.add_argument("--progress", required=True)
    args = ap.parse_args()
    assert os.getpriority(os.PRIO_PROCESS,0) >= 19
    resource.setrlimit(resource.RLIMIT_AS,(768*1024**2,768*1024**2))
    started = time.monotonic()
    n,edges = instance(args.case)
    positions = [(v,v) for v in range(n)] + [a for u,v in edges for a in ((u,v),(v,u))]
    ref,hc,factor_count,signed = inventory(n,edges,positions)
    h = (n & -n).bit_length()-1
    t = args.bits+h
    supports = matching_supports(n,positions,min(n,2*t-2))
    stop = min(args.stop,len(supports))
    c,_ = determinant_hc_cnf(n,edges,with_sign=False)
    z = [c.names[f"position_{u}_{v}"] for u,v in positions]
    queries = nonzero = 0
    residue = reference_residue = 0
    modulus = 1<<t
    rows = []
    for index in range(args.start,stop):
        chosen = supports[index]
        coef = coefficient([positions[i] for i in chosen])
        assert coef % (1<<((len(chosen)+1)//2)) == 0
        if coef % modulus:
            nonzero += 1
            bits = sum(1<<i for i in chosen)
            expected = sum(weight for support,weight in ref.items() if support & bits == bits)
            actual = exact_count(c.nvars,c.clauses+[(z[i],) for i in chosen])
            assert actual == expected,(args.case,index,chosen,actual,expected)
            residue = (residue+coef*actual)%modulus
            reference_residue = (reference_residue+coef*expected)%modulus
            queries += 1
        if (index+1)%50 == 0:
            with open(args.progress,"a") as f:
                f.write(json.dumps({"index_exclusive":index+1,"queries":queries,
                                    "elapsed_seconds":time.monotonic()-started})+"\n")
    answer = None
    if args.start == 0 and stop == len(supports):
        assert residue == signed%modulus
        assert residue%(1<<h) == 0
        answer = ((residue>>h)*pow(n>>h,-1,1<<args.bits))%(1<<args.bits)
        assert answer == hc%(1<<args.bits)
    print(json.dumps({"status":"PASS","args":vars(args),"n":n,"m":len(edges),
                      "start":args.start,"stop":stop,"total_supports":len(supports),
                      "queries":queries,"nonzero_coefficients":nonzero,"t":t,
                      "residue":residue,"reference_residue":reference_residue,
                      "true_hc":hc,"two_factors":factor_count,"signed_reference":signed,
                      "recovered_answer":answer,"N":c.nvars,"M":len(c.clauses),
                      "elapsed_seconds":time.monotonic()-started},sort_keys=True))


if __name__ == "__main__":
    main()
