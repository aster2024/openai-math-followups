"""Finite regression checks of exact identities, never evidence for asymptotics."""
import json
import math
import time
from collections import Counter
from fractions import Fraction
from pathlib import Path


def main():
    started = time.time()
    counts = Counter()
    examples = {}
    for delta in range(-80, 81):
        if delta == 0:
            continue
        H = abs(delta)
        for u in range(3, 101, 2):
            for v in range(3, 101, 2):
                if math.gcd(u, v) != 1 or math.gcd(u * v, H) != 1:
                    continue
                # det((u,v),(c,d))=delta, 0 <= c < u.
                c = (-delta * pow(v, -1, u)) % u
                d = (delta + c * v) // u
                assert u * d - v * c == delta
                assert math.gcd(u, c) == 1
                rho = v * pow(u, -1, H) % H if H > 1 else 0
                assert (d - rho * c) % H == 0
                beta = Fraction(c, u)
                eps = Fraction(delta, u * v)
                if abs(eps) < 1:
                    k = d // v
                    assert k in (-1, 0, 1)
                    cs = (1 + k) * v - d
                    ds = (1 + k) * u - c
                    assert 0 < cs < v
                    assert v * ds - u * cs == delta
                    assert Fraction(cs, v) == 1 + k - beta - eps
                    counts[f"swap_branch_{k}"] += 1
                    examples.setdefault(f"swap_branch_{k}", [delta, u, v, c, d])
                for z1, z2 in ((1, 0), (0, 1), (1, 2), (-1, 2), (2, 1), (3, -2)):
                    q1 = u * z1 + c * z2
                    q2 = v * z1 + d * z2
                    tau = Fraction(q1, u)
                    assert q2 == v * tau + Fraction(delta * z2, u)
                    assert u * q2 - v * q1 == delta * z2
                    lattice_primitive = math.gcd(z1, z2) == 1
                    plane_primitive = math.gcd(q1, q2) == 1
                    assert plane_primitive == (lattice_primitive and math.gcd(q1, H) == 1)
                    if H % 2:
                        assert (q1 % 2 == q2 % 2 == 1) == (z1 % 2 == 1 and z2 % 2 == 0)
                    else:
                        assert (q1 % 2 == q2 % 2 == 1) == ((z1 + c * z2) % 2 == 1)
                    counts["relative_coordinate_checks"] += 1
                counts["root_checks"] += 1

    # The two possible orientations disappear from the cofactor square exactly.
    for eps_sign in (-1, 1):
        for h in range(-25, 26):
            if h == 0:
                continue
            delta = -eps_sign * h
            for a, b in ((3, 5), (5, 7), (7, 11), (9, 25)):
                for j in range(-12, 13):
                    if j == 0:
                        continue
                    k0 = delta + a * j
                    l0 = delta + b * j
                    if min(k0, l0) <= 0:
                        continue
                    assert b * k0 - a * l0 == delta * (b - a)
                    assert Fraction(eps_sign * k0 + h, a) == Fraction(eps_sign * l0 + h, b)
                    counts["cofactor_checks"] += 1

    # In a fixed slope cell, lattice determinant spacing, not H itself,
    # controls the occupancy. These are only small finite examples.
    occupancy = []
    for H in (1, 2, 3, 5, 8, 12, 35, 64):
        D, M, N = 3, 4, 11
        width = Fraction(H, D * M * M)
        cells = Counter()
        for rho in range(H):
            if math.gcd(rho, H) != 1:
                continue
            for u in range(D * M, 16 * D * M + 1):
                for v in range(N, 2 * N + 1):
                    if (v - rho * u) % H:
                        continue
                    # coordinates in basis ((1,rho),(0,H))
                    if math.gcd(u, (v - rho * u) // H) != 1:
                        continue
                    cells[rho, int(Fraction(v, u) // width)] += 1
        occupancy.append({"H": H, "max_occupancy": max(cells.values(), default=0), "D": D})

    result = {
        "status": "PASS_FINITE_IDENTITIES_ONLY",
        "elapsed_seconds": time.time() - started,
        "counts": dict(counts),
        "branch_examples_delta_u_v_c_d": examples,
        "slope_cell_examples": occupancy,
        "asymptotic_claims_verified": False,
    }
    Path("AFFINE_GEOMETRY_CHECK.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    import contextlib
    import io
    import os
    os.chdir(Path(__file__).resolve().parent)
    with contextlib.redirect_stdout(io.StringIO()):
        main()
    receipt = json.loads(Path('AFFINE_GEOMETRY_CHECK.json').read_text())
    print('check_affine_geometry' + " " + receipt["status"] + "; finite identities only")
