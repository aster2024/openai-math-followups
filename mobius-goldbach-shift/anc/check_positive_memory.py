"""Exact finite checks for the new positive active-memory model.

This checks a one-group, J=0, capped model, including repeated memory
types and active/memory overlaps. It proves no asymptotic estimate.
"""
import itertools
import json
import math
import time
from collections import defaultdict
from fractions import Fraction as F
from functools import lru_cache
from pathlib import Path

PRIMES = (3, 5)
V = sum((F(1, p) for p in PRIMES), F(0))
NU = {p: 1 / (V * (p + 1)) for p in PRIMES}
RHO = F(1, 4)
SQRT_RHO = F(1, 2)
CAP = 2
POSITIONS = tuple((u, v) for u in (1, 2, 3, 5) for v in range(-2, 3)
                  if math.gcd(u, v) == 1)
ROOT = POSITIONS.index((1, 0))
TYPES = tuple((p, ell) for p in PRIMES for ell in range(p + 1))
TYPE_ID = {v: i for i, v in enumerate(TYPES)}
MEMORIES = tuple(m for k in range(CAP + 1)
                 for m in itertools.combinations_with_replacement(range(len(TYPES)), k))


def line(z, p):
    u, v = z
    return p if u % p == 0 else v * pow(u, -1, p) % p


@lru_cache(None)
def measure(state):
    zi, active, memory = state
    ans = NU[active]
    counts = defaultdict(int)
    for ty in memory:
        counts[ty] += 1
        ans *= NU[TYPES[ty][0]]
    for n in counts.values():
        ans /= math.factorial(n)
    return ans


def hits(zi, memory):
    return sum(line(POSITIONS[zi], TYPES[t][0]) == TYPES[t][1] for t in memory)


def geometry(zi, zj, source, target):
    u, v = POSITIONS[zi]
    a, b = POSITIONS[zj]
    determinant = u*b-v*a
    return F(determinant == source-target) + F(abs(determinant) <= 8, 2)


@lru_cache(None)
def records(state):
    zi, source, memory = state
    out = defaultdict(F)
    hs = hits(zi, memory)
    for zj in range(len(POSITIONS)):
        for target in PRIMES:
            if source == target:
                continue
            geom = geometry(zi, zj, source, target)
            if not geom:
                continue
            target_type = TYPE_ID[target, line(POSITIONS[zj], target)]
            multiplicity = memory.count(target_type)
            for recall in (0, 1):
                if recall and not multiplicity:
                    continue
                base = list(memory)
                if recall:
                    base.remove(target_type)
                arrival = F(multiplicity) / V if recall else NU[target]
                for append in (0, 1):
                    final = list(base)
                    if append:
                        final.append(TYPE_ID[source, line(POSITIONS[zi], source)])
                    if len(final) > CAP:
                        continue
                    final = tuple(sorted(final))
                    target_state = (zj, target, final)
                    coeff = geom * arrival * SQRT_RHO ** (hs + hits(zj, final))
                    out[target_state, append, recall] += coeff
    return dict(out)


def adjoints():
    states = tuple((zi, p, m) for zi in range(len(POSITIONS))
                   for p in PRIMES for m in MEMORIES)
    row_max = F(0)
    columns = defaultdict(F)
    checked = 0
    repeated_checked = 0
    for state in states:
        w = 2 ** len(state[2])
        row = F(0)
        for (target, append, recall), coeff in records(state).items():
            reverse = records(target).get((state, recall, append), F(0))
            actual_adjoint = coeff * measure(state) / measure(target)
            assert actual_adjoint == reverse * V ** (append-recall), (
                state, target, append, recall, actual_adjoint, reverse)
            row += coeff * 2 ** len(target[2]) / w
            columns[target] += actual_adjoint * w / 2 ** len(target[2])
            checked += 1
            repeated_checked += len(set(state[2])) < len(state[2])
        row_max = max(row_max, row)
    return {"states": len(states), "operation_records": checked,
            "records_from_repeated_memory": repeated_checked,
            "max_weighted_row_sum": str(row_max),
            "max_weighted_column_sum": str(max(columns.values()))}


def canonical_dp(steps, distinct):
    # Initial inner-product measure charges the active prime once.
    current = defaultdict(F)
    for p in PRIMES:
        current[((ROOT, p, ()), 1 << PRIMES.index(p))] += NU[p]
    for _ in range(steps):
        nxt = defaultdict(F)
        for (state, mask), value in current.items():
            for (target, append, recall), coeff in records(state).items():
                bit = 1 << PRIMES.index(target[1])
                if distinct and not recall and mask & bit:
                    continue
                nxt[(target, mask | bit)] += value * coeff
        current = nxt
    return sum((value for (state, mask), value in current.items()
                if state[0] == ROOT and not state[2]), F(0))


def direct_active_sum(steps):
    total = F(0)
    # Two primes plus the cross-edge exclusion force alternating active lists.
    for first in PRIMES:
        other = next(p for p in PRIMES if p != first)
        active = tuple(first if j % 2 == 0 else other for j in range(steps+1))
        for middle in itertools.product(range(len(POSITIONS)), repeat=steps-1):
            path = (ROOT, *middle, ROOT)
            factor = F(1)
            for j in range(steps):
                factor *= geometry(path[j], path[j+1], active[j], active[j+1])
            for p in PRIMES:
                times = [j for j, q in enumerate(active) if p == q]
                if not times:
                    continue
                ell = line(POSITIONS[path[times[0]]], p)
                if any(line(POSITIONS[path[j]], p) != ell for j in times):
                    factor = F(0)
                    break
                runs = sum(j == 0 or times[j] != times[j-1]+1 for j in range(len(times)))
                factor *= F(1, p+1) / V ** runs
                for j in range(times[0]+1, times[-1]):
                    if active[j] != p and line(POSITIONS[path[j]], p) == ell:
                        factor *= RHO
            total += factor
    return total


def main():
    started = time.time()
    adj = adjoints()
    path_checks = []
    for steps in (2, 4):
        direct = direct_active_sum(steps)
        represented = canonical_dp(steps, True)
        enlarged = canonical_dp(steps, False)
        assert direct == represented
        assert represented <= enlarged
        path_checks.append({"edges": steps, "direct_active_sum": str(direct),
                            "canonical_memory_sum": str(represented),
                            "enlarged_positive_sum": str(enlarged)})
    parameter_checks = []
    for a in (F(1,10), F(1,5), F(1,3), F(49,100), F(4999,10000), F(499999,1000000)):
        theta = (max(a,F(1,10))+F(1,2))/2
        j = (1-2*theta)/10
        r, b = theta+2*j, theta+3*j
        assert r-j-theta == j > 0
        assert b-r == j
        assert 1-(r+j+theta) == 1-(b+theta) == 7*j
        assert a < theta < F(1,2) < F(3,4)
        parameter_checks.append({k:str(v) for k,v in (("a",a),("theta",theta),("j",j),("r",r),("b",b))})
    result = {"status": "PASS_FINITE_POSITIVE_MEMORY_IDENTITIES_ONLY",
              "scope": "one group, J=0, two primes, memory cap 2, fifteen primitive positions including projective infinity for both primes",
              "adjoints": adj, "path_checks": path_checks,
              "half_exponent_parameter_checks": parameter_checks,
              "elapsed_seconds": time.time()-started,
              "asymptotic_claims_verified": False}
    Path("POSITIVE_MEMORY_CHECK.json").write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    import contextlib
    import io
    import os
    os.chdir(Path(__file__).resolve().parent)
    with contextlib.redirect_stdout(io.StringIO()):
        main()
    receipt = json.loads(Path('POSITIVE_MEMORY_CHECK.json').read_text())
    print('check_positive_memory' + " " + receipt["status"] + "; finite identities only")
