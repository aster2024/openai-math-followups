"""Finite hostile check of the inactive-prime remainder, independently of memory.

The original and J=1 memory tests have no never-active primes on many paths.
Here a five-prime pool and one active slot leave inactive primes. We compare
exact joint-line enumeration with the factorized Bonferroni expectations.
"""
from collections import defaultdict
from fractions import Fraction as F
from functools import lru_cache
from itertools import product
from math import factorial
from pathlib import Path
import json
import time

PRIMES = (3, 5, 7, 11, 13)
POSITIONS = ((1, 0), (1, 1), (3, 1), (5, 1))
N = 4
V = sum((F(1, p) for p in PRIMES), F())
Q = (F(1, 2), F(1, 4), F(1, 4), F(1, 4), F(1, 2))
JOINT_DENOMINATOR = 1
for p in PRIMES:
    JOINT_DENOMINATOR *= p + 1


def line(zi, p):
    u, v = POSITIONS[zi]
    return p if u % p == 0 else v * pow(u, -1, p) % p


LINES = {(zi, p): line(zi, p) for zi in range(len(POSITIONS)) for p in PRIMES}


def elementary(values):
    result = [F(1)] + [F()] * len(values)
    for value in values:
        for degree in range(len(values), 0, -1):
            result[degree] += result[degree - 1] * value
    return result


@lru_cache(None)
def geometry(zi, zj, p, q):
    u, v = POSITIONS[zi]
    r, s = POSITIONS[zj]
    det = u * s - v * r
    return F(det == p-q) + F(abs(det) <= 13, 13)


@lru_cache(None)
def local(path, p, times):
    if times:
        ell = LINES[path[times[0]], p]
        if any(LINES[path[j], p] != ell for j in times):
            return F(), F(), F()
        runs = sum(k == 0 or t != times[k - 1] + 1 for k, t in enumerate(times))
        factor = F(1, p + 1) / V ** runs
        upper = factor
        for j in range(N + 1):
            if j not in times and LINES[path[j], p] == ell:
                factor *= Q[j]
                if times[0] < j < times[-1]:
                    upper *= Q[j]
        return factor, upper, F()
    deficit = F()
    for ell in range(p + 1):
        damping = F(1)
        for j in range(N + 1):
            if LINES[path[j], p] == ell:
                damping *= Q[j]
        deficit += 1-damping
    return F(1), F(1), deficit / (p+1)


def factorized(path, active):
    A = upper = F(1)
    means = []
    for p in PRIMES:
        times = tuple(j for j, q in enumerate(active) if p == q)
        factor, upper_factor, deficit = local(path, p, times)
        A *= factor
        upper *= upper_factor
        if not times:
            means.append(deficit)
    elementary_means = elementary(means)
    full = A
    for mean in means:
        full *= 1-mean
    return A, upper, elementary_means, full


def exact_joint(path, active):
    totals = [F() for _ in range(5)]  # active, full, e1, e2, e3
    active_times = {p: tuple(j for j, q in enumerate(active) if p == q) for p in PRIMES}
    runs = {p: sum(k == 0 or t != ts[k-1] + 1 for k, t in enumerate(ts))
            for p, ts in active_times.items()}
    for lines in product(*(range(p+1) for p in PRIMES)):
        factor = F(1) / V ** sum(runs.values())
        deficits = []
        for p, ell in zip(PRIMES, lines):
            ts = active_times[p]
            if ts:
                if any(LINES[path[j], p] != ell for j in ts):
                    factor = F()
                    break
                for j in range(N+1):
                    if j not in ts and LINES[path[j], p] == ell:
                        factor *= Q[j]
            else:
                damping = F(1)
                for j in range(N+1):
                    if LINES[path[j], p] == ell:
                        damping *= Q[j]
                deficits.append(1-damping)
        if not factor:
            continue
        values = elementary(deficits)
        full = factor
        for deficit in deficits:
            full *= 1-deficit
        totals[0] += factor
        totals[1] += full
        for degree in range(1, 4):
            totals[degree+1] += factor * (values[degree] if degree < len(values) else 0)
    return tuple(value / JOINT_DENOMINATOR for value in totals)


def main():
    started = time.monotonic()
    diagnostics = [((0, 0, 0, 0, 0), (3, 5, 3, 5, 3)),
                   ((0, 1, 0, 1, 0), (3, 5, 3, 5, 3)),
                   ((0, 2, 0, 2, 0), (3, 5, 7, 5, 3)),
                   ((0, 3, 0, 3, 0), (5, 3, 7, 3, 5))]
    for path, active in diagnostics:
        A, upper, values, full = factorized(path, active)
        expected = (A, full, *(A * (values[k] if k < len(values) else 0) for k in range(1, 4)))
        assert exact_joint(path, active) == expected
    print(f'JOINT_INACTIVE_LINES_PASS diagnostics={len(diagnostics)} line_assignments_each={JOINT_DENOMINATOR}', flush=True)

    sums = defaultdict(F)
    paths = nonzero = with_inactive = 0
    U = F(N+1) * sum((F(1, p+1) for p in PRIMES), F())
    for middle in product(range(len(POSITIONS)), repeat=N-1):
        path = (0, *middle, 0)
        for active in product(PRIMES, repeat=N+1):
            if any(active[j] == active[j+1] for j in range(N)):
                continue
            geom = F(1)
            for j in range(N):
                geom *= geometry(path[j], path[j+1], active[j], active[j+1])
            A, upper, values, full = factorized(path, active)
            assert A <= upper
            paths += 1
            if not A:
                continue
            nonzero += 1
            with_inactive += len(set(active)) < len(PRIMES)
            sums['active'] += geom*A
            sums['active_upper'] += geom*upper
            sums['full'] += geom*full
            for degree in range(1, 4):
                previous = A * sum(((-1)**k * values[k] for k in range(min(degree, len(values)))), F())
                next_value = A * sum(((-1)**k * values[k] for k in range(min(degree+1, len(values)))), F())
                lower, higher = sorted((previous, next_value))
                assert lower <= full <= higher
                eb = values[degree] if degree < len(values) else F()
                assert higher-lower == A*eb
                assert eb <= U**degree / factorial(degree)
                sums[f'remainder_{degree}'] += geom*A*eb
    for degree in range(1, 4):
        assert sums[f'remainder_{degree}'] <= sums['active'] * U**degree / factorial(degree)
    result = dict(status='PASS_FINITE_INACTIVE_PRIME_BONFERRONI_ONLY',
                  diagnostic_line_assignments=len(diagnostics)*JOINT_DENOMINATOR,
                  geometric_paths=paths, nonzero_active_paths=nonzero,
                  nonzero_paths_with_inactive_primes=with_inactive,
                  exact_sums={k: str(v) for k, v in sums.items()},
                  uniform_deficit_sum_bound=str(U),
                  elapsed_seconds=time.monotonic()-started,
                  asymptotic_claims_verified=False)
    Path('INACTIVE_BONFERRONI.json').write_text(json.dumps(result, indent=2)+'\n')
    print(f'BONFERRONI_MODEL_PASS paths={paths} nonzero={nonzero} with_inactive={with_inactive} degrees=1,2,3', flush=True)
    print('PASS_FINITE_INACTIVE_PRIME_BONFERRONI_ONLY', flush=True)


if __name__ == "__main__":
    import contextlib
    import io
    import os
    os.chdir(Path(__file__).resolve().parent)
    with contextlib.redirect_stdout(io.StringIO()):
        main()
    receipt = json.loads(Path('INACTIVE_BONFERRONI.json').read_text())
    print('check_inactive_bonferroni' + " " + receipt["status"] + "; finite models only")
