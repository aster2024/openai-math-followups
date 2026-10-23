"""Independent delayed-charge oracle and forward-history upper bound.

No append/recall choices, factorial memory state, or adjoint is used here.
An inactive prime's hit count is charged only if it becomes active again;
unreturned suffixes are discarded. This is a third implementation of (9.3).
"""
from collections import defaultdict
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations, product
from math import factorial, prod
from pathlib import Path
import argparse
import json
import time


def run(case, steps):
    if case == 'j1_three':
        groups = ((3, 5, 7),)
        size = 2
        positions = ((1, 0), (1, 6), (1, 10), (1, 14), (1, 20),
                     (3, 1), (5, 1), (7, 1), (1, 3), (1, 5), (1, 7))
        comparison, cutoff = F(1, 13), 20
    elif case == 'j2_four':
        groups = ((3, 5, 7, 11),)
        size = 3
        positions = ((1, 0), (1, 6), (1, 10), (1, 14), (1, 20),
                     (1, 22), (1, 33), (3, 1), (5, 1), (7, 1), (11, 1))
        comparison, cutoff = F(1, 3), 30
    elif case == 'k2_j1':
        groups = ((3, 5, 7), (11, 13, 17))
        size = 2
        positions = ((1, 0), (1, 33), (1, 39), (1, 51), (1, 55),
                     (1, 65), (1, 85), (1, 77), (1, 91), (1, 119),
                     (1, 1782), (1, -1782),
                     (3, 1), (5, 1), (7, 1), (11, 1), (13, 1))
        comparison, cutoff = F(1, 33), 330
    elif case == 'j2_crt':
        groups = ((3, 5, 7, 11),)
        size = 3
        # Every affine residue tuple modulo 3*5*7*11, plus infinity for each.
        positions = tuple((1, v) for v in range(3 * 5 * 7 * 11)) + (
            (3, 1), (5, 1), (7, 1), (11, 1))
        comparison, cutoff = F(1, 3), 30
    else:
        raise ValueError(case)
    started = time.monotonic()
    primes = tuple(p for group in groups for p in group)
    pindex = {p: i for i, p in enumerate(primes)}
    group_of = {p: gi for gi, group in enumerate(groups) for p in group}
    masses = tuple(sum((F(1, p) for p in group), F()) for group in groups)
    nu = {p: F(1, p + 1) / masses[group_of[p]] for p in primes}
    lists = tuple(product(*(tuple(combinations(group, size)) for group in groups)))
    permutations = factorial(size) ** len(groups)
    choice_average = F(1, size ** len(groups))

    def line(zi, p):
        u, v = positions[zi]
        return p if u % p == 0 else v * pow(u, -1, p) % p
    lines = {(zi, p): line(zi, p) for zi in range(len(positions)) for p in primes}

    @lru_cache(None)
    def shared_buckets(shared_primes):
        buckets = defaultdict(list)
        for zj in range(len(positions)):
            signature = tuple(lines[zj, p] for p in shared_primes)
            buckets[signature].append(zj)
        return buckets

    @lru_cache(None)
    def edges(zi, active):
        result = []
        for departures in product(*active):
            shared = tuple(tuple(p for p in group if p != departing)
                           for group, departing in zip(active, departures))
            D = prod(p for group in shared for p in group)
            shared_primes = tuple(p for group in shared for p in group)
            signature = tuple(lines[zi, p] for p in shared_primes)
            candidates = shared_buckets(shared_primes)[signature]
            old_product = prod(departures)
            incoming_pools = tuple(tuple(p for p in pool if p not in current)
                                   for pool, current in zip(groups, active))
            for arrivals in product(*incoming_pools):
                new_lists = tuple(tuple(sorted((*keep, arriving)))
                                  for keep, arriving in zip(shared, arrivals))
                new_product = prod(arrivals)
                for zj in candidates:
                    u, v = positions[zi]
                    r, s = positions[zj]
                    det = u * s - v * r
                    if det % D:
                        continue
                    geom = (F(det == D * (old_product - new_product))
                            + comparison * (abs(det // D) <= cutoff))
                    if geom:
                        result.append((zj, new_lists, arrivals, geom * choice_average,
                                       departures, geom))
        return tuple(result)

    # This maximum fixes all labels before summing target positions.
    geom_max = F()
    for zi in range(len(positions)):
        for active in lists:
            totals = defaultdict(F)
            for zj, target, arrivals, coefficient, departures, geom in edges(zi, active):
                totals[departures, arrivals] += geom
            geom_max = max(geom_max, max(totals.values(), default=F()))

    def initial_weight(active):
        return F(permutations) * prod(nu[p] for group in active for p in group)
    initial_mass = sum((initial_weight(active) for active in lists), F())
    assert initial_mass <= 1

    def exact_delayed(rho):
        current = defaultdict(F)
        for active in lists:
            anchors = [-1] * len(primes)
            for group in active:
                for p in group:
                    anchors[pindex[p]] = lines[0, p]
            current[0, active, tuple(anchors), (0,) * len(primes)] += initial_weight(active)
        counts = []
        for depth in range(steps):
            nxt = defaultdict(F)
            for (zi, active, anchors, pending), value in current.items():
                for zj, target, arrivals, coefficient, _, _ in edges(zi, active):
                    next_anchors = list(anchors)
                    next_pending = list(pending)
                    factor = coefficient
                    for p in arrivals:
                        pi = pindex[p]
                        if anchors[pi] < 0:
                            next_anchors[pi] = lines[zj, p]
                            factor *= nu[p]
                        elif anchors[pi] != lines[zj, p]:
                            break
                        else:
                            factor *= rho ** pending[pi] / masses[group_of[p]]
                        next_pending[pi] = 0
                    else:
                        now_active = {p for group in target for p in group}
                        if rho != 1:
                            for p in primes:
                                pi = pindex[p]
                                if p not in now_active and next_anchors[pi] >= 0:
                                    next_pending[pi] += lines[zj, p] == next_anchors[pi]
                        nxt[zj, target, tuple(next_anchors), tuple(next_pending)] += value * factor
            current = nxt
            counts.append(len(current))
            if depth % 2 == 1:
                print(f'DELAYED_PROGRESS case={case} rho={rho} edge={depth+1} states={len(current)}', flush=True)
            if time.monotonic() - started > 840:
                raise TimeoutError('Bounded computation reached its internal 840-second limit')
        result = sum((value for (zi, _, _, _), value in current.items() if zi == 0), F())
        return result, counts

    def coarse_history():
        current = defaultdict(F)
        for active in lists:
            mask = sum(1 << pindex[p] for group in active for p in group)
            current[0, active, mask] += initial_weight(active)
        for depth in range(steps):
            nxt = defaultdict(F)
            for (zi, active, mask), value in current.items():
                for zj, target, arrivals, coefficient, _, _ in edges(zi, active):
                    new_mask = mask
                    factor = coefficient
                    for p in arrivals:
                        bit = 1 << pindex[p]
                        factor *= F(1) / masses[group_of[p]] if mask & bit else nu[p]
                        new_mask |= bit
                    nxt[zj, target, new_mask] += value * factor
            current = nxt
        closed = sum((value for (zi, _, _), value in current.items() if zi == 0), F())
        return closed, sum(current.values(), F())

    exact, sizes = exact_delayed(F(1, 4))
    without_damping, _ = exact_delayed(F(1))
    coarse_closed, coarse_open = coarse_history()
    upper = prod(geom_max * prod(1 + F(depth) / V for V in masses)
                 for depth in range(steps))
    assert exact <= without_damping <= coarse_closed <= coarse_open <= upper
    if case == 'j1_three' and steps in (2, 4, 6):
        oracle = {2: F(12195579375, 274852741696),
                  4: F(482986103330390625, 7492960684170610688),
                  6: F(13770606694716670025390625, 102135528043276547085074432)}
        assert exact == oracle[steps], (exact, oracle[steps])
    result = dict(status='PASS_FINITE_DELAYED_CHARGE_AND_HISTORY_BOUND_ONLY',
                  case=case, edges=steps, K=len(groups), J=size-1,
                  exact_active_sum=str(exact), no_damping_sum=str(without_damping),
                  coarse_closed=str(coarse_closed), coarse_open=str(coarse_open),
                  forward_product_bound=str(upper), geom_max=str(geom_max),
                  layer_states=sizes, elapsed_seconds=time.monotonic()-started,
                  asymptotic_claims_verified=False)
    path = Path(f'HISTORY_{case}_{steps}.json')
    path.write_text(json.dumps(result, indent=2) + '\n')
    print(f'HISTORY_BOUND_PASS case={case} K={len(groups)} J={size-1} edges={steps}', flush=True)
    print(json.dumps(result, sort_keys=True), flush=True)


if __name__ == "__main__":
    import contextlib
    import io
    import os
    os.chdir(Path(__file__).resolve().parent)
    cases = (("j1_three", 6), ("j2_four", 12), ("k2_j1", 12), ("j2_crt", 8))
    with contextlib.redirect_stdout(io.StringIO()):
        for case, steps in cases:
            run(case, steps)
    print("check_forward_histories PASS: J=1, J=2, K=2, full CRT; finite histories only")
