import sys as _local_sys
from pathlib import Path as _local_Path
_local_sys.path.insert(0, str(_local_Path(__file__).resolve().parent))
#!/usr/bin/env python3
"""Check the block-count bound in Section 6.1 a = O(M/B + 1) for the greedy light/heavy blocking:
explicitly a <= 4*M/B + 1 (heavy <= M/B, runs <= heavy+1, run blocks <= 2*M_run/B + 1)."""
import random, sys
sys.path.insert(0, str(__import__('pathlib').Path(__file__).resolve().parent))
from p6_sign_check import greedy_blocks
rng = random.Random(7); worst = 0
for t in range(20000):
    N = rng.randint(1, 300); B = rng.randint(1, 60)
    deg = [max(1, int(rng.paretovariate(rng.choice([0.7, 1.2, 2.5])))) for _ in range(N)]
    M = sum(deg)
    lab, heavy = greedy_blocks(deg, B)
    a = max(lab) + 1
    # every light block has load <= B; blocks are contiguous intervals
    loads = {}
    for i, u in enumerate(lab): loads[u] = loads.get(u, 0) + deg[i]
    assert all(loads[u] <= B for u in loads if not heavy[u])
    assert lab == sorted(lab)
    assert a <= 4 * M / B + 1, (N, B, M, a)
    worst = max(worst, a / (M / B + 1))
print(f"block-count bound a <= 4M/B+1 holds on 20000 random degree sequences; max a/(M/B+1) = {worst:.3f}")
