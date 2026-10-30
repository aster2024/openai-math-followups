"""All labelled graphs at a specified small order; actual #3CNF vs brute HC.

For every weight layer the generic #DPLL count is compared with an
independent enumeration of 2-factors, and its parity with a permutation
enumeration of Hamilton cycles.  Labels and graph inclusion masks are
exhaustive; graph families are not sampled.
"""
import argparse
import json
import sys
import time
from collections import Counter
from itertools import combinations, permutations
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
from cnf_circuits import Circuit, cut_count_cnf, count_dimacs_dpll


def brute_hc_hist(n, edges, weights):
    lookup = {tuple(sorted(e)): w for e, w in zip(edges, weights)}
    hist = Counter()
    if n < 3:
        return hist
    for middle in permutations(range(1, n)):
        if middle[0] >= middle[-1]:
            continue
        order = (0,) + middle + (0,)
        pairs = [tuple(sorted((order[i], order[i + 1]))) for i in range(n)]
        if all(e in lookup for e in pairs):
            hist[sum(lookup[e] for e in pairs)] += 1
    return hist


def brute_cut_hist(n, edges, weights):
    hist = Counter()
    for indices in combinations(range(len(edges)), n):
        adj = [[] for _ in range(n)]
        for i in indices:
            u, v = edges[i]
            adj[u].append(v)
            adj[v].append(u)
        if any(len(a) != 2 for a in adj):
            continue
        seen = set()
        components = 0
        for root in range(n):
            if root in seen:
                continue
            components += 1
            stack = [root]
            seen.add(root)
            while stack:
                for v in adj[stack.pop()]:
                    if v not in seen:
                        seen.add(v)
                        stack.append(v)
        hist[sum(weights[i] for i in indices)] += 1 << (components - 1)
    return hist


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, required=True)
    ap.add_argument("--start", type=int, default=0)
    ap.add_argument("--stop", type=int)
    ap.add_argument("--max-edges", type=int)
    ap.add_argument("--weight-range", type=int, default=4)
    ap.add_argument("--only-unweighted", action="store_true")
    ap.add_argument("--progress")
    ap.add_argument("--whole-word",action="store_true")
    args = ap.parse_args()
    if args.whole_word:
        Circuit.weighted_sum = Circuit.weighted_sum_whole_word
    start_time = time.monotonic()
    all_edges = list(combinations(range(args.n), 2))
    stop = min(args.stop or 1 << len(all_edges), 1 << len(all_edges))
    graphs = queries = nonham_factors = 0
    sum_hc = 0
    max_variables = max_clauses = 0
    start_mask = args.start
    for mask in range(start_mask, stop):
        if args.max_edges is not None and mask.bit_count() > args.max_edges:
            continue
        chosen = [i for i in range(len(all_edges)) if mask >> i & 1]
        edges = [all_edges[i] for i in chosen]
        weights = [1 if args.only_unweighted else (7 * i + 3) % args.weight_range + 1
                   for i in chosen]
        hc = brute_hc_hist(args.n, edges, weights)
        cuts = brute_cut_hist(args.n, edges, weights)
        assert all((cuts[t] & 1) == (hc[t] & 1) for t in set(cuts) | set(hc))
        nonham_factors += sum(cuts[t] > hc[t] for t in cuts)
        sum_hc += sum(hc.values())
        base, output = cut_count_cnf(args.n, edges, weights)
        assert max(map(len, base.clauses), default=0) <= 3
        max_variables = max(max_variables, base.nvars)
        max_clauses = max(max_clauses, len(base.clauses))
        targets = range(args.n * max(weights, default=1) + 1)
        if args.only_unweighted:
            targets = [args.n]
        for target in targets:
            unit_clauses = [(bit if target >> i & 1 else -bit,)
                            for i, bit in enumerate(output)]
            impossible = target >= 1 << len(output)
            counted = count_dimacs_dpll(base.nvars, base.clauses +
                                       ([()] if impossible else unit_clauses))
            assert counted == cuts[target], (args.n, mask, target, counted, cuts[target])
            assert counted % 2 == hc[target] % 2, (args.n, mask, target, counted, hc[target])
            queries += 1
        graphs += 1
        if args.progress and (mask + 1) % 128 == 0:
            Path(args.progress).write_text(json.dumps({
                "status": "RUNNING", "start": start_mask, "next_mask": mask + 1,
                "graphs_completed": graphs, "queries_completed": queries,
                "elapsed_seconds": time.monotonic() - start_time}, sort_keys=True))
    print(json.dumps({"status": "PASS", "n": args.n,
                      "start": start_mask, "stop": stop, "max_edges": args.max_edges,
                      "graphs": graphs, "weight_layer_cnf_queries": queries,
                      "mode": "unweighted" if args.only_unweighted else "weighted",
                      "arithmetic": "whole_word" if args.whole_word else "carry_scan",
                      "sum_brute_hc": sum_hc, "layers_with_nonhamiltonian_2factors": nonham_factors,
                      "max_N": max_variables, "max_M": max_clauses,
                      "elapsed_seconds": time.monotonic() - start_time}, sort_keys=True))


if __name__ == "__main__":
    main()
