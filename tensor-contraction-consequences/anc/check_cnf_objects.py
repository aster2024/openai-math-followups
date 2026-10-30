import argparse
import json
import sys
import time
from itertools import combinations
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
from cnf_circuits import connected_object_cnf, count_dimacs_dpll


def components(n, vertices, edges):
    unseen = {v for v in range(n) if vertices >> v & 1}
    result = []
    while unseen:
        root = min(unseen)
        block = {root}
        unseen.remove(root)
        stack = [root]
        while stack:
            v = stack.pop()
            for a, b in edges:
                other = b if a == v else a if b == v else None
                if other in unseen:
                    unseen.remove(other)
                    block.add(other)
                    stack.append(other)
        result.append(block)
    return result


def expected_counts(n, edges, mode):
    cuts = truth = 0
    all_bits = (1 << n) - 1
    for U in range(1 << n):
        if mode != "fvs" and U & 1 == 0:
            continue
        inside = [(a, b) for a, b in edges if U >> a & 1 and U >> b & 1]
        if mode == "cover" and any(not (U >> a & 1 or U >> b & 1) for a, b in edges):
            continue
        if mode == "dominating":
            dominated = U
            for a, b in edges:
                if U >> a & 1:
                    dominated |= 1 << b
                if U >> b & 1:
                    dominated |= 1 << a
            if dominated != all_bits:
                continue
        if mode == "steiner":
            if not (U >> (n - 1) & 1):
                continue
            for F in combinations(inside, U.bit_count() - 1):
                cc = len(components(n, U, F))
                cuts += 1 << (cc - 1)
                truth += cc == 1
        elif mode == "fvs":
            comps = components(n, U, inside)
            for M in range(1 << n):
                if M & ~U or len(inside) + M.bit_count() != U.bit_count():
                    continue
                unmarked = sum(not any(M >> v & 1 for v in block) for block in comps)
                cuts += 1 << unmarked
                forest = len(inside) == U.bit_count() - len(comps)
                one_marker = all(sum(M >> v & 1 for v in block) == 1 for block in comps)
                truth += forest and one_marker
        else:
            cc = len(components(n, U, inside))
            cuts += 1 << (cc - 1)
            truth += cc == 1
    return cuts, truth


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=4)
    ap.add_argument("--start", type=int, default=0)
    ap.add_argument("--stop", type=int)
    args = ap.parse_args()
    start = time.monotonic()
    potential = list(combinations(range(args.n), 2))
    stop = min(args.stop or 1 << len(potential), 1 << len(potential))
    queries = max_n = max_m = 0
    totals = {mode: {"cuts": 0, "true_objects": 0} for mode in ("steiner", "cover", "dominating", "fvs")}
    for mask in range(args.start, stop):
        edges = [e for i, e in enumerate(potential) if mask >> i & 1]
        for mode in totals:
            c = connected_object_cnf(args.n, edges, mode, terminals=(0, args.n - 1))
            actual = count_dimacs_dpll(c.nvars, c.clauses)
            cuts, true_objects = expected_counts(args.n, edges, mode)
            assert actual == cuts, (args.n, mask, mode, actual, cuts)
            assert actual % 2 == true_objects % 2
            assert max(map(len, c.clauses), default=0) <= 3
            totals[mode]["cuts"] += cuts
            totals[mode]["true_objects"] += true_objects
            max_n = max(max_n, c.nvars)
            max_m = max(max_m, len(c.clauses))
            queries += 1
    print(json.dumps({"status": "PASS", "n": args.n,
                      "start": args.start, "stop": stop,
                      "graphs": stop - args.start, "cnf_queries": queries,
                      "totals": totals, "max_N": max_n, "max_M": max_m,
                      "elapsed_seconds": time.monotonic() - start}, sort_keys=True))


if __name__ == "__main__":
    main()
