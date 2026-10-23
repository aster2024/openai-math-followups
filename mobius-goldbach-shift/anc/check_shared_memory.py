"""Independent exact J=1 test of the positive active-list/memory identity.

The direct path oracle uses complete time histories and run counts, never memory.
The second calculation uses append/recall operations with factorial measures.
Only finite identities are tested; there is no asymptotic certification.
"""
from collections import Counter, defaultdict
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations, combinations_with_replacement
import json
from math import factorial
from pathlib import Path
import time

PRIMES = (3, 5, 7)
V = sum((F(1, p) for p in PRIMES), F())
NU = {p: F(1, p + 1) / V for p in PRIMES}
RHO = F(1, 4)
ROOT = 0
POSITIONS = ((1, 0), (1, 6), (1, 10), (1, 14), (1, 20),
             (3, 1), (5, 1), (7, 1), (1, 3), (1, 5), (1, 7))
LISTS = tuple(combinations(PRIMES, 2))
CAP = 2
TYPES = tuple((p, line) for p in PRIMES for line in range(p + 1))
TYPE_ID = {pair: index for index, pair in enumerate(TYPES)}
MEMORIES = tuple(m for k in range(CAP + 1)
                 for m in combinations_with_replacement(range(len(TYPES)), k))


def line(zi, p):
    u, v = POSITIONS[zi]
    return p if u % p == 0 else v * pow(u, -1, p) % p


LINES = {(zi, p): line(zi, p) for zi in range(len(POSITIONS)) for p in PRIMES}


@lru_cache(None)
def geometry(zi, zj, shared, departing, arriving):
    u, v = POSITIONS[zi]
    r, s = POSITIONS[zj]
    det = u * s - v * r
    if det % shared:
        return F()
    return F(det == shared * (departing - arriving)) + F(abs(det // shared) <= 20, 13)


@lru_cache(None)
def list_edges(zi, active):
    out = []
    for departing in active:
        shared = next(p for p in active if p != departing)
        for arriving in PRIMES:
            if arriving in active:
                continue
            target_list = tuple(sorted((shared, arriving)))
            for zj in range(len(POSITIONS)):
                if LINES[zi, shared] != LINES[zj, shared]:
                    continue
                geom = geometry(zi, zj, shared, departing, arriving)
                if geom:
                    # S on an ordered list chooses its unshared slot uniformly.
                    out.append((zj, target_list, departing, arriving, geom / 2))
    return tuple(out)


@lru_cache(None)
def hits(zi, memory):
    return sum(LINES[zi, TYPES[t][0]] == TYPES[t][1] for t in memory)


@lru_cache(None)
def measure(state):
    zi, active, memory = state
    # The two ordered active lists give the same permutation-invariant state.
    ans = F(factorial(len(active)))
    for p in active:
        ans *= NU[p]
    for ty, n in Counter(memory).items():
        ans *= NU[TYPES[ty][0]] ** n / factorial(n)
    return ans


@lru_cache(None)
def memory_edges(state):
    zi, active, memory = state
    out = defaultdict(F)
    for zj, target_list, departing, arriving, geom in list_edges(zi, active):
        arrival_type = TYPE_ID[arriving, LINES[zj, arriving]]
        departure_type = TYPE_ID[departing, LINES[zi, departing]]
        multiplicity = memory.count(arrival_type)
        for recall in (0, 1):
            if recall and not multiplicity:
                continue
            for append in (0, 1):
                final = list(memory)
                if recall:
                    final.remove(arrival_type)
                if append:
                    final.append(departure_type)
                if len(final) > CAP:
                    continue
                final = tuple(sorted(final))
                arrival_factor = F(multiplicity) / V if recall else NU[arriving]
                damping = F(1, 2) ** (hits(zi, memory) + hits(zj, final))
                target = (zj, target_list, final)
                out[target, append, recall] += geom * arrival_factor * damping
    return dict(out)


def check_adjoints():
    checked = repeated = overlap = 0
    row_max = F()
    columns = defaultdict(F)
    for zi in range(len(POSITIONS)):
        for active in LISTS:
            for memory in MEMORIES:
                state = (zi, active, memory)
                source_weight = 2 ** len(memory)
                row = F()
                for (target, append, recall), coeff in memory_edges(state).items():
                    reverse = memory_edges(target).get((state, recall, append), F())
                    adj = coeff * measure(state) / measure(target)
                    assert adj == reverse * V ** (append - recall), (
                        state, target, append, recall, adj, reverse)
                    row += coeff * 2 ** len(target[2]) / source_weight
                    columns[target] += adj * source_weight / 2 ** len(target[2])
                    checked += 1
                    repeated += len(set(memory)) < len(memory)
                    overlap += any(TYPES[t][0] in active for t in memory)
                row_max = max(row_max, row)
    result = dict(states=len(POSITIONS) * len(LISTS) * len(MEMORIES),
                  records=checked, repeated_memory_records=repeated,
                  active_memory_overlap_records=overlap,
                  weighted_row_max=str(row_max),
                  weighted_column_max=str(max(columns.values())))
    print('J1_ADJOINT_PASS ' + json.dumps(result, sort_keys=True), flush=True)
    return result


def direct_oracle(steps):
    total = F()
    leaves = 0
    for initial in LISTS:
        def visit(path, lists, coefficient):
            nonlocal total, leaves
            if len(path) == steps + 1:
                if path[-1] != ROOT:
                    return
                leaves += 1
                factor = F(factorial(len(initial)))
                for p in PRIMES:
                    times = [j for j, active in enumerate(lists) if p in active]
                    if not times:
                        continue
                    ell = LINES[path[times[0]], p]
                    if any(LINES[path[j], p] != ell for j in times):
                        return
                    runs = sum(i == 0 or t != times[i - 1] + 1
                               for i, t in enumerate(times))
                    factor *= F(1, p + 1) / V ** runs
                    for j in range(times[0] + 1, times[-1]):
                        if p not in lists[j] and LINES[path[j], p] == ell:
                            factor *= RHO
                total += coefficient * factor
                return
            for zj, active, _, _, geom in list_edges(path[-1], lists[-1]):
                if len(path) == steps and zj != ROOT:
                    continue
                visit(path + (zj,), lists + (active,), coefficient * geom)
        visit((ROOT,), (initial,), F(1))
    return total, leaves


def memory_dp(steps, distinct):
    current = defaultdict(F)
    for active in LISTS:
        mask = sum(1 << PRIMES.index(p) for p in active)
        state = (ROOT, active, ())
        current[state, mask] = measure(state)
    for _ in range(steps):
        nxt = defaultdict(F)
        for (state, mask), value in current.items():
            for (target, append, recall), coeff in memory_edges(state).items():
                arriving = next(p for p in target[1] if p not in state[1])
                bit = 1 << PRIMES.index(arriving)
                if distinct and not recall and mask & bit:
                    continue
                nxt[target, mask | bit] += value * coeff
        current = nxt
    return sum((value for (state, _), value in current.items()
                if state[0] == ROOT and not state[2]), F())


def main():
    start = time.monotonic()
    adjoints = check_adjoints()
    paths = []
    for steps in (2, 4, 6):
        direct, leaves = direct_oracle(steps)
        canonical = memory_dp(steps, True)
        enlarged = memory_dp(steps, False)
        assert direct == canonical, (steps, direct, canonical)
        assert canonical <= enlarged
        result = dict(edges=steps, direct=str(direct), canonical=str(canonical),
                      enlarged=str(enlarged), closed_path_leaves=leaves)
        print('J1_PATH_PASS ' + json.dumps(result, sort_keys=True), flush=True)
        paths.append(result)
    output = dict(status='PASS_FINITE_SHARED_LIST_IDENTITIES_ONLY', J=1, K=1,
                  adjoints=adjoints, paths=paths, elapsed_seconds=time.monotonic()-start,
                  asymptotic_claims_verified=False)
    Path('SHARED_MEMORY_LISTS.json').write_text(json.dumps(output, indent=2) + '\n')
    print('PASS_FINITE_SHARED_LIST_IDENTITIES_ONLY', flush=True)


if __name__ == "__main__":
    import contextlib
    import io
    import os
    os.chdir(Path(__file__).resolve().parent)
    with contextlib.redirect_stdout(io.StringIO()):
        main()
    receipt = json.loads(Path('SHARED_MEMORY_LISTS.json').read_text())
    print('check_shared_memory' + " " + receipt["status"] + "; finite models only")
