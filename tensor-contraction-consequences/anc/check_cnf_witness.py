"""Runs the actual parity-layer and witness algorithm with a generic #CNF oracle."""
import argparse
import json
import random
import sys
import time
from itertools import combinations, product
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
from cnf_circuits import cut_count_cnf, count_dimacs_dpll
from check_cnf_layers import brute_hc_hist


def oracle(c, output, target, fixed=()):
    if target >= 1 << len(output):
        return 0
    conditions = [(b if target >> i & 1 else -b,) for i, b in enumerate(output)]
    return count_dimacs_dpll(c.nvars, c.clauses + conditions + [(b,) for b in fixed])


def find(c, output, n, edges, weights):
    calls = 0
    for target in range(n * max(weights, default=1) + 1):
        calls += 1
        if oracle(c, output, target) % 2:
            fixed = []
            chosen = []
            for i, e in enumerate(edges):
                bit = c.names[f"edge_{i}"]
                calls += 1
                if oracle(c, output, target, fixed + [-bit]) % 2:
                    fixed.append(-bit)
                else:
                    fixed.append(bit)
                    chosen.append(i)
            assert oracle(c, output, target, fixed) % 2 == 1
            deg = [0] * n
            adj = [[] for _ in range(n)]
            for i in chosen:
                u, v = edges[i]
                deg[u] += 1
                deg[v] += 1
                adj[u].append(v)
                adj[v].append(u)
            assert deg == [2] * n
            seen = {0}
            queue = [0]
            while queue:
                for v in adj[queue.pop()]:
                    if v not in seen:
                        seen.add(v)
                        queue.append(v)
            assert len(seen) == n
            assert sum(weights[i] for i in chosen) == target
            return chosen, target, calls
    return None, None, calls


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=4)
    ap.add_argument("--range", type=int, default=2)
    ap.add_argument("--limit", type=int)
    ap.add_argument("--optimisation", action="store_true")
    args = ap.parse_args()
    start = time.monotonic()
    n = args.n
    edges = list(combinations(range(n), 2))
    costs = [(i * 3 + 1) % 5 for i in range(len(edges))]
    optimum = min(brute_hc_hist(n, edges, costs))
    attempts = successes = optimal = queries = isolated = 0
    for w in product(range(1, args.range + 1), repeat=len(edges)):
        if args.limit is not None and attempts >= args.limit:
            break
        weights = list(w)
        if args.optimisation:
            P = n * args.range + 1
            weights = [P * cost + weight for cost, weight in zip(costs, weights)]
        c, output = cut_count_cnf(n, edges, weights)
        chosen, target, calls = find(c, output, n, edges, weights)
        histogram = brute_hc_hist(n, edges, weights)
        unique_min = histogram[min(histogram)] == 1
        isolated += unique_min
        assert not unique_min or chosen is not None
        assert (chosen is not None) == any(v % 2 for v in histogram.values())
        if chosen is not None:
            successes += 1
            cost = sum(costs[i] for i in chosen)
            optimal += cost == optimum
            if args.optimisation and unique_min:
                assert cost == optimum
        queries += calls
        attempts += 1
    if args.limit is None:
        assert isolated >= (args.range - 1) ** len(edges)
    print(json.dumps({"status": "PASS", "n": n, "m": len(edges),
                      "weight_range": args.range, "optimisation": args.optimisation,
                      "exhaustive_weights": args.limit is None,
                      "attempts": attempts, "unique_minimum_attempts": isolated,
                      "witnesses_found": successes, "optimal_witnesses": optimal,
                      "cnf_oracle_calls": queries,
                      "elapsed_seconds": time.monotonic() - start}, sort_keys=True))


if __name__ == "__main__":
    main()
