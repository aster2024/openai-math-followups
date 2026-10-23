"""Exact finite CRT/weight identities and rational exponent bookkeeping."""
import itertools
import json
import math
import time
from collections import Counter
from fractions import Fraction as F
from pathlib import Path


def product(xs):
    result = F(1)
    for x in xs:
        result *= x
    return result


def weight(k, V):
    return F(0) if k == 0 else F(k, 2 ** (k - 1)) / V


def moments(primes):
    V = sum((F(1, p) for p in primes), F(0))
    first = sum((F(1, p - 1) * product(1 - F(1, 2 * (q - 1))
                 for q in primes if q != p) for p in primes), F(0)) / V
    second = F(0)
    for mask in itertools.product((0, 1), repeat=len(primes)):
        probability = product(F(1, p - 1) if bit else 1 - F(1, p - 1)
                              for p, bit in zip(primes, mask))
        second += probability * weight(sum(mask), V) ** 2
    return V, first, second


def check_crt():
    universe = (3, 5, 7, 11, 13, 17)
    modulus = math.prod(universe)
    units = [u for u in range(modulus) if math.gcd(u, modulus) == 1]
    receipts = []
    for h in (2, 6, 10, 22, 26, 30, 34):
        rough = tuple(p for p in (3, 5) if h % p)
        bands = (tuple(p for p in (7, 11) if h % p),
                 tuple(p for p in (13, 17) if h % p))
        V1, m1, s1 = moments(bands[0])
        V2, m2, s2 = moments(bands[1])
        rough_mass = product(1 - F(1, p - 1) for p in rough)
        expected_variance = rough_mass * (s1 / m1**2 + s2 / m2**2 - 2) / 4
        for sign in (-1, 1):
            counts = Counter()
            for u in units:
                n = sign * u + h
                rflag = all(n % p for p in rough)
                k1 = sum(n % p == 0 for p in bands[0])
                k2 = sum(n % p == 0 for p in bands[1])
                counts[rflag, k1, k2] += 1
            measured = [F(0) for _ in range(5)]
            for (rflag, k1, k2), count in counts.items():
                if not rflag:
                    continue
                probability = F(count, len(units))
                w1, w2 = weight(k1, V1), weight(k2, V2)
                for i, value in enumerate((1, w1, w2, w1*w2,
                                           ((w1/m1+w2/m2)/2-1)**2)):
                    measured[i] += probability * value
            expected = [rough_mass, rough_mass*m1, rough_mass*m2,
                        rough_mass*m1*m2, expected_variance]
            assert measured == expected, (h, sign, measured, expected)
            receipts.append({"h": h, "orientation": sign,
                             "rough_mass": str(rough_mass),
                             "relative_variance": str(expected_variance / rough_mass)})
    return {"modulus": modulus, "unit_classes": len(units),
            "parameter_pairs": len(receipts), "receipts": receipts}


def check_weights():
    bound = 30000
    spf = list(range(bound + 1))
    for p in range(2, math.isqrt(bound) + 1):
        if spf[p] == p:
            for n in range(p*p, bound + 1, p):
                if spf[n] == n:
                    spf[n] = p
    mu = [1] * (bound + 1)
    liouville = [1] * (bound + 1)
    for n in range(2, bound + 1):
        p = spf[n]
        m = n // p
        liouville[n] = -liouville[m]
        mu[n] = 0 if m % p == 0 else -mu[m]
    bands = ((7, 11), (13, 17))
    primes = tuple(p for band in bands for p in band)
    Vs = [sum((F(1, p) for p in band), F(0)) for band in bands]
    products = tuple(p*q for p in bands[0] for q in bands[1])
    norm = product(Vs)
    overlap_examples = 0
    for n in range(1, bound + 1):
        counts = [sum(n % p == 0 for p in band) for band in bands]
        W = product(weight(k, V) for k, V in zip(counts, Vs))
        omega = sum(counts)
        rflag = n % 3 != 0 and n % 5 != 0
        mu_rhs = F(0)
        lambda_coprime = F(0)
        overlap_mass = F(0)
        for a in products:
            if n % a:
                continue
            ell = n // a
            assert rflag == (ell % 3 != 0 and ell % 5 != 0)
            if math.gcd(a, ell) == 1:
                rho_factor = F(1, 2 ** sum(ell % p == 0 for p in primes))
                mu_rhs += mu[ell] * rho_factor / norm
                lambda_coprime += liouville[ell] * rho_factor / norm
            else:
                overlap_mass += F(1, 2 ** (omega - 2)) / norm
        assert mu[n] * W == mu_rhs
        assert liouville[n] * W - lambda_coprime == liouville[n] * overlap_mass
        assert 0 <= overlap_mass <= W
        overlap_examples += overlap_mass != 0
    return {"positive_integers_checked": bound, "overlap_examples": overlap_examples}


def check_parameters():
    receipts = []
    for a in (F(1, 100), F(1, 10), F(1, 5), F(3, 10),
              F(33, 100), F(333, 1000), F(3333, 10000), F(333333, 1000000)):
        theta = (max(a, F(1, 10)) + F(1, 3)) / 2
        j = (1 - 3*theta) / 8
        r = (1 + theta) / 4
        b = (1 + theta) / 2
        assert 0 < j < r < 1
        assert a < theta < F(1, 3) < F(1, 2)
        assert r-j-theta == j
        assert b-r-j-theta == j
        assert 1-b-theta == 4*j
        assert max(r+j+theta, r, j) < 1
        receipts.append({name: str(value) for name, value in
                         (("a", a), ("theta", theta), ("j", j),
                          ("r", r), ("b", b), ("root_modulus_exponent", b+theta))})
    return receipts


def main():
    start = time.time()
    result = {"status": "PASS_FINITE_IDENTITIES_ONLY", "crt": check_crt(),
              "weights": check_weights(), "parameters": check_parameters(),
              "asymptotic_claims_verified": False}
    result["elapsed_seconds"] = time.time()-start
    Path("ROUGH_PARAMETER_CHECK.json").write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps({"status": result["status"], "elapsed_seconds": result["elapsed_seconds"],
                      "crt_unit_classes": result["crt"]["unit_classes"],
                      "crt_parameter_pairs": result["crt"]["parameter_pairs"],
                      "weights": result["weights"], "parameter_choices": len(result["parameters"])}))


if __name__ == "__main__":
    import contextlib
    import io
    import os
    os.chdir(Path(__file__).resolve().parent)
    with contextlib.redirect_stdout(io.StringIO()):
        main()
    receipt = json.loads(Path('ROUGH_PARAMETER_CHECK.json').read_text())
    print('check_rough_and_parameters' + " " + receipt["status"] + "; finite identities only")
