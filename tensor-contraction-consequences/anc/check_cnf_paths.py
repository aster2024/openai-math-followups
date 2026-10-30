import argparse
import json
import sys
import time
from collections import Counter
from itertools import combinations, permutations
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
from cnf_circuits import cut_count_cnf, count_dimacs_dpll
from check_cnf_objects import components


def brute_hist(n, edges, weights, path, directed):
    lookup = {e if directed else tuple(sorted(e)): w for e, w in zip(edges, weights)}
    result = Counter()
    middle = range(1, n - 1) if path else range(1, n)
    for rest in permutations(middle):
        order = (0,) + rest + ((n - 1,) if path else (0,))
        pairs = [(order[i], order[i + 1]) for i in range(len(order) - 1)]
        if not directed:
            pairs = [tuple(sorted(e)) for e in pairs]
        if all(e in lookup for e in pairs):
            result[sum(lookup[e] for e in pairs)] += 1
    return result


def cut_hist(n, edges, weights, path, directed):
    result = Counter()
    size = n - int(path)
    for F in combinations(range(len(edges)), size):
        deg_in, deg_out = [0] * n, [0] * n
        for i in F:
            u, v = edges[i]
            if directed:
                deg_out[u] += 1
                deg_in[v] += 1
            else:
                deg_in[u] += 1
                deg_in[v] += 1
        if directed:
            if deg_in != ([0] + [1] * (n - 1) if path else [1] * n):
                continue
            if deg_out != ([1] * (n - 1) + [0] if path else [1] * n):
                continue
        else:
            expected = [1] + [2] * (n - 2) + [1]
            if deg_in != expected:
                continue
        cc = len(components(n, (1 << n) - 1, [edges[i] for i in F]))
        result[sum(weights[i] for i in F)] += 1 << (cc - 1)
    return result


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, required=True)
    ap.add_argument("--directed", action="store_true")
    ap.add_argument("--path", action="store_true")
    ap.add_argument("--start", type=int, default=0)
    ap.add_argument("--stop", type=int)
    ap.add_argument("--max-edges", type=int)
    args = ap.parse_args()
    assert args.path or args.directed
    start = time.monotonic()
    n = args.n
    potential = [(u, v) for u in range(n) for v in range(n) if u != v] if args.directed else list(combinations(range(n), 2))
    stop = min(args.stop or 1 << len(potential), 1 << len(potential))
    queries = graphs = extra_layers = 0
    for mask in range(args.start, stop):
        if args.max_edges is not None and mask.bit_count() > args.max_edges:
            continue
        indices = [i for i in range(len(potential)) if mask >> i & 1]
        edges = [potential[i] for i in indices]
        weights = [(7 * i + 1) % 3 + 1 for i in indices]
        expected = brute_hist(n, edges, weights, args.path, args.directed)
        cuts = cut_hist(n, edges, weights, args.path, args.directed)
        extra_layers += sum(cuts[t] > expected[t] for t in cuts)
        c, output = cut_count_cnf(n, edges, weights,
                                  endpoints=(0, n - 1) if args.path else None,
                                  directed=args.directed)
        for target in range((n - int(args.path)) * max(weights, default=1) + 1):
            if target >= 1 << len(output):
                counted = 0
            else:
                conditions = [(b if target >> i & 1 else -b,) for i, b in enumerate(output)]
                counted = count_dimacs_dpll(c.nvars, c.clauses + conditions)
            assert counted == cuts[target], (n, mask, target, counted, cuts[target])
            assert counted % 2 == expected[target] % 2
            queries += 1
        graphs += 1
    print(json.dumps({"status": "PASS", "n": n, "directed": args.directed,
                      "path": args.path, "start": args.start, "stop": stop,
                      "graphs": graphs, "cnf_queries": queries,
                      "layers_with_disconnected_candidates": extra_layers,
                      "elapsed_seconds": time.monotonic() - start}, sort_keys=True))


if __name__ == "__main__":
    main()
