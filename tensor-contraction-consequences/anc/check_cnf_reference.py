"""Independent literal counter, exact graph references, and adversarial checks.

The circuit construction is compared with separate literal and graph references.  Run with nice -n 19 and
an external timeout <= 300 seconds.  All numbers are exact integers.
"""
import argparse
from collections import Counter
from functools import lru_cache
from itertools import combinations, product
import json
import os
from pathlib import Path
import random
import resource
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parent))
from cnf_circuits import Circuit, cut_count_cnf, determinant_hc_cnf, connected_object_cnf
PROGRESS = None


def progress(data):
    if PROGRESS:
        with open(PROGRESS, "a") as f:
            f.write(json.dumps({"utc":time.strftime("%Y-%m-%dT%H:%M:%SZ",time.gmtime()),
                                **data},sort_keys=True)+"\n")


def exact_count(n, clauses):
    """Bitset Shannon expansion; canonical clauses and bounded memoization.

    Handles tautologies, duplicate literals, absent declared variables, empty
    clauses, and units.  No pure-literal elimination (unsound for counting).
    """
    normalized = []
    for clause in clauses:
        pos = neg = 0
        for lit in clause:
            assert 1 <= abs(lit) <= n
            if lit > 0:
                pos |= 1 << (lit - 1)
            else:
                neg |= 1 << (-lit - 1)
        if not pos & neg:
            normalized.append((pos, neg))
    initial = tuple(sorted(set(normalized)))

    @lru_cache(maxsize=4096)
    def visit(current, remaining):
        while True:
            yes = no = 0
            for pos, neg in current:
                bits = pos | neg
                if not bits:
                    return 0
                if bits & (bits - 1) == 0:
                    yes |= pos
                    no |= neg
            if yes & no:
                return 0
            if not yes | no:
                break
            remaining &= ~(yes | no)
            current = tuple(sorted(set((p & ~no, q & ~yes) for p, q in current
                                       if not (p & yes or q & no))))
        if not current:
            return 1 << remaining.bit_count()
        used = 0
        for p, q in current:
            used |= p | q
        free = (remaining & ~used).bit_count()
        remaining &= used
        p, q = min(current, key=lambda c: (c[0] | c[1]).bit_count())
        v = (p | q) & -(p | q)
        return (visit(tuple(sorted(current + ((v, 0),))), remaining) +
                visit(tuple(sorted(current + ((0, v),))), remaining)) << free

    return visit(initial, (1 << n) - 1)


def truth_count(n, clauses):
    return sum(all(any(bool(mask & (1 << (abs(lit) - 1))) == (lit > 0)
                       for lit in clause) for clause in clauses)
               for mask in range(1 << n))


def reference_graph(n, edges, weights, endpoints=None, directed=False):
    """Enumerate selected edge sets and use union-find; no cycle permutations."""
    cuts, solutions, objects = Counter(), Counter(), {}
    size = n - 1 if endpoints is not None else n
    for chosen in combinations(range(len(edges)), size):
        parent = list(range(n))
        def root(v):
            while parent[v] != v:
                parent[v] = parent[parent[v]]
                v = parent[v]
            return v
        incoming = [0] * n
        outgoing = [0] * n
        for i in chosen:
            u, v = edges[i]
            outgoing[u] += 1
            incoming[v] += 1
            parent[root(v)] = root(u)
        if directed:
            if any(incoming[v] != (0 if endpoints and v == endpoints[0] else 1)
                   or outgoing[v] != (0 if endpoints and v == endpoints[1] else 1)
                   for v in range(n)):
                continue
        elif any(incoming[v] + outgoing[v] != (1 if endpoints and v in endpoints else 2)
                 for v in range(n)):
            continue
        cc = len({root(v) for v in range(n)})
        total = sum(weights[i] for i in chosen)
        cuts[total] += 1 << (cc - 1)
        if cc == 1:
            solutions[total] += 1
        objects[chosen] = (total, cc)
    return cuts, solutions, objects


def literal_constraints(bits, target):
    if target < 0 or target >= 1 << len(bits):
        return [()]
    return [(b if target >> j & 1 else -b,) for j, b in enumerate(bits)]


def gate_checks(rng):
    random_cnfs = 0
    for n in range(0, 9):
        for _ in range(150):
            clauses = [tuple(rng.choice((-1, 1)) * rng.randint(1, n)
                             for _ in range(rng.randrange(5)))
                       for _ in range(rng.randrange(15))] if n else [()] * rng.randrange(2)
            assert exact_count(n, clauses) == truth_count(n, clauses)
            random_cnfs += 1
    gate_assignments = 0
    for op in ("and", "or", "xor"):
        for a, b in product(range(6), repeat=2):
            c = Circuit()
            x, y = [c.new_var(primary=True) for _ in range(2)]
            literals = (x, -x, y, -y, c.zero, c.one)
            z = c.gate(op, literals[a], literals[b])
            for xv, yv, zv in product((0, 1), repeat=3):
                vals = (xv, 1-xv, yv, 1-yv, 0, 1)
                expected = {"and": vals[a] & vals[b], "or": vals[a] | vals[b],
                            "xor": vals[a] ^ vals[b]}[op] == zv
                clauses = c.clauses + [(x if xv else -x,), (y if yv else -y,),
                                       (z if zv else -z,)]
                assert exact_count(c.nvars, clauses) == expected, (op, a, b, xv, yv, zv)
                gate_assignments += 1
    return {"random_cnf_reference_cases": random_cnfs,
            "gate_truth_and_extension_cases": gate_assignments}


def arithmetic_checks(rng, start, stop):
    circuits = queries = assignments = 0
    max_n = 0
    for case in range(start, stop):
        p = case % 9
        weights = [rng.getrandbits(1 + case % 32) for _ in range(p)]
        if case % 5 == 0:
            weights = [((1 << (1 + case % 16)) - 1)] * p
        if case % 7 == 0:
            weights = [0] * p
        negative = [rng.randrange(2) for _ in range(p)]
        hist = Counter()
        for mask in range(1 << p):
            hist[sum(w * (((mask >> i) & 1) ^ negative[i])
                     for i, w in enumerate(weights))] += 1
        for method in ("weighted_sum", "weighted_sum_whole_word"):
            c = Circuit()
            xs = [c.new_var(primary=True) for _ in range(p)]
            literals = [-x if neg else x for x, neg in zip(xs, negative)]
            output = getattr(c, method)(literals, weights, 1 + case % 4)
            assert max(map(len, c.clauses)) <= 3
            assert exact_count(c.nvars, c.clauses) == (1 << p)
            queries += 1
            targets = set(hist)
            targets.update((-1, 0, sum(weights), sum(weights) + 1, 1 << len(output)))
            for target in sorted(targets):
                got = exact_count(c.nvars, c.clauses + literal_constraints(output, target))
                assert got == hist[target], (case, method, target, got, hist[target])
                queries += 1
            # Fix every primary assignment in small circuits: exactly one extension.
            if p <= 4:
                for mask in range(1 << p):
                    fixed = [(x if mask >> i & 1 else -x,) for i, x in enumerate(xs)]
                    expected = sum(w * (((mask >> i) & 1) ^ negative[i])
                                   for i, w in enumerate(weights))
                    assert exact_count(c.nvars, c.clauses + fixed +
                                       literal_constraints(output, expected)) == 1
                    assignments += 1
            max_n = max(max_n, c.nvars)
            circuits += 1
        progress({"mode":"arithmetic","completed_case":case,"circuits":circuits,
                  "queries":queries,"fixed_extensions":assignments})
    return {"circuits": circuits, "literal_count_queries": queries,
            "fixed_input_unique_extensions": assignments, "max_N": max_n}


def graph_checks(rng, start, stop, n):
    possible = list(combinations(range(n), 2))
    queries = graph_count = nonhc_layers = hc_total = 0
    max_n = max_m = 0
    for mask in range(start, min(stop, 1 << len(possible))):
        edges = [e for j, e in enumerate(possible) if mask >> j & 1]
        if len(edges) > 2 * n:
            continue
        weights = [1 + rng.randrange(max(2, 2 * len(edges))) for _ in edges]
        cuts, hc, _ = reference_graph(n, edges, weights)
        c, output = cut_count_cnf(n, edges, weights)
        targets = set(cuts) | set(hc)
        targets.update((-1, 0, n * max(weights, default=1) + 1))
        # Also check weights with no candidate, rather than only positive layers.
        targets.update(rng.randrange(max(1, sum(weights) + 1)) for _ in range(3))
        for target in targets:
            got = exact_count(c.nvars, c.clauses + literal_constraints(output, target))
            assert got == cuts[target], (n, mask, weights, target, got, cuts[target])
            assert got % 2 == hc[target] % 2
            queries += 1
        assert max(map(len, c.clauses)) <= 3
        nonhc_layers += sum(cuts[t] != hc[t] for t in cuts)
        hc_total += sum(hc.values())
        max_n, max_m = max(max_n, c.nvars), max(max_m, len(c.clauses))
        graph_count += 1
        if graph_count % 32 == 0:
            progress({"mode":"graphs","completed_mask":mask,"graphs":graph_count,
                      "queries":queries,"nonhc_layers":nonhc_layers})
    return {"graphs": graph_count, "literal_count_queries": queries,
            "nonhamiltonian_layers": nonhc_layers, "sum_hc": hc_total,
            "max_N": max_n, "max_M": max_m}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("mode", choices=("gates", "arithmetic", "graphs"))
    ap.add_argument("--start", type=int, default=0)
    ap.add_argument("--stop", type=int, default=50)
    ap.add_argument("--n", type=int, default=6)
    ap.add_argument("--seed", type=int, default=10300931)
    ap.add_argument("--progress")
    args = ap.parse_args()
    global PROGRESS
    PROGRESS = args.progress
    assert os.getpriority(os.PRIO_PROCESS, 0) >= 19
    resource.setrlimit(resource.RLIMIT_AS, (768 * 1024**2, 768 * 1024**2))
    started = time.monotonic()
    rng = random.Random(args.seed + args.start)
    if args.mode == "gates":
        result = gate_checks(rng)
    elif args.mode == "arithmetic":
        result = arithmetic_checks(rng, args.start, args.stop)
    else:
        result = graph_checks(rng, args.start, args.stop, args.n)
    print(json.dumps({"status": "PASS", "args": vars(args), **result,
                      "elapsed_seconds": time.monotonic() - started}, sort_keys=True))


if __name__ == "__main__":
    main()
