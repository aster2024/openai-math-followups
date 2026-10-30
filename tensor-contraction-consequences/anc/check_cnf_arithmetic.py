import argparse
import json
import random
import sys
import time
from itertools import product
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
from cnf_circuits import Circuit, count_dimacs_dpll


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--max-inputs", type=int, default=9)
    args = ap.parse_args()
    start = time.monotonic()
    rng = random.Random(20261030)
    assignments = circuits = dpll_cases = 0
    for d in range(args.max_inputs + 1):
        for digit_bits in (1, 2, 3, 4):
            for case in range(8):
                weights = [rng.randrange(0, (d + 2) ** 3) for _ in range(d)]
                c = Circuit()
                xs = [c.new_var(primary=True) for _ in range(d)]
                count = c.popcount(xs)
                weighted = c.weighted_sum(xs, weights, digit_bits)
                assert max(map(len, c.clauses), default=0) <= 3
                for values in product((False, True), repeat=d):
                    evaluated = c.evaluate(values)
                    assert c.satisfies(evaluated)
                    assert c.value_of(count, evaluated) == sum(values)
                    assert c.value_of(weighted, evaluated) == sum(
                        w * x for w, x in zip(weights, values))
                    assignments += 1
                if d <= 4 and case == 0:
                    target = rng.randrange(sum(weights) + 1)
                    c.equal_constant(weighted, target)
                    expected = sum(sum(w * x for w, x in zip(weights, values)) == target
                                   for values in product((False, True), repeat=d))
                    assert count_dimacs_dpll(c.nvars, c.clauses) == expected
                    dpll_cases += 1
                circuits += 1
    print(json.dumps({"status": "PASS", "circuits": circuits,
                      "assignments": assignments, "independent_dpll_cases": dpll_cases,
                      "elapsed_seconds": time.monotonic() - start}, sort_keys=True))


if __name__ == "__main__":
    main()
