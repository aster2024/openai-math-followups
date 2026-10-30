"""Concrete gate ledger at radix changes and high degree; no SAT extrapolation."""
import argparse
from collections import Counter
import json
import os
from pathlib import Path
import random
import resource
import sys
import time
sys.path.insert(0, str(Path(__file__).resolve().parent))
from cnf_circuits import Circuit, cut_count_cnf


class CountOnlyList:
    def __init__(self):
        self.n = 0
    def append(self, item):
        self.n += 1
    def extend(self, items):
        self.n += len(items)
    def __len__(self):
        return self.n


def budget(p, weights, b, h):
    q = (p + 1 - 1).bit_length()
    A = max(weights, default=0)
    Q = (p * A).bit_length() + 1
    buckets = sum(len({(w >> (j * b)) & ((1 << b) - 1) for w in weights} - {0})
                  for j in range(h))
    return 10*h*p + 5*buckets*b*(q+b+1) + 5*buckets*Q + 5*(buckets+h)*(q+b+1)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--max-power", type=int, default=14)
    ap.add_argument("--degree", type=int, default=4)
    args = ap.parse_args()
    assert os.getpriority(os.PRIO_PROCESS, 0) >= 19
    resource.setrlimit(resource.RLIMIT_AS, (768*1024**2, 768*1024**2))
    start = time.monotonic()
    rng = random.Random(101030)
    sizes = sorted({0, 1, 2, 3, 7, 15, 31, 63, 127, 253, 254, 255, 256,
                    *[2**k for k in range(9, args.max_power+1)]})
    rows = []
    for p in sizes:
        for pattern in ("zero", "max", "random", "distinct"):
            max_weight = (p+2)**args.degree
            weights = ([0]*p if pattern == "zero" else [max_weight]*p if pattern == "max"
                       else [rng.randrange(max_weight+1) for _ in range(p)] if pattern == "random"
                       else [((i+1)*max(1, max_weight//max(1,p))) for i in range(p)])
            c = Circuit()
            # Retain actual clauses/gates through the first base-4 boundary.
            store = p <= 256
            if not store:
                c.gates = CountOnlyList()
                c.clauses = CountOnlyList()
                c.clauses.append((-c.zero,))
            xs = [c.new_var(primary=True) for _ in range(p)]
            output = c.weighted_sum(xs, weights)
            stat = c.stats["weighted_sums"][0]
            bound = budget(p, weights, stat["digit_bits"], stat["digits"])
            assert len(c.gates) <= bound, (p, pattern, len(c.gates), bound)
            assert c.nvars == p+1+len(c.gates)
            assert len(c.clauses) <= 4*len(c.gates)+1
            if store:
                for inputs in ([0]*p, [1]*p, [i%2 for i in range(p)],
                               [rng.randrange(2) for _ in range(p)]):
                    values = c.evaluate(inputs)
                    assert c.satisfies(values)
                    assert c.value_of(output, values) == sum(w*x for w,x in zip(weights,inputs))
            rows.append({"p":p,"pattern":pattern,"N":c.nvars,"M":len(c.clauses),
                         "gates":len(c.gates),"explicit_bound":bound,**stat,
                         "assignment_checks":4 if store else 0})
    # Wheel graphs: sparse while maximum degree is n-1.
    wheels = []
    for n in (8,16,32,64,128,256):
        edges = [(0,v) for v in range(1,n)] + [(v,1+v%(n-1)) for v in range(1,n)]
        c, out = cut_count_cnf(n, edges, [2*len(edges)]*len(edges))
        wheels.append({"n":n,"m":len(edges),"max_degree":n-1,"N":c.nvars,
                       "M":len(c.clauses),"max_width":max(map(len,c.clauses))})
        assert max(map(len,c.clauses)) <= 3
    print(json.dumps({"status":"PASS","args":vars(args),"arithmetic":rows,
                      "sparse_high_degree":wheels,"elapsed_seconds":time.monotonic()-start},sort_keys=True))


if __name__ == "__main__":
    main()
