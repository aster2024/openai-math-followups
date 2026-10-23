"""Exact finite identities for the progression corollary; no asymptotic claims."""
import itertools
import json
import math
import time
from collections import Counter, defaultdict
from fractions import Fraction as F
from pathlib import Path


def factor(n):
    result = {}
    p = 2
    while p * p <= n:
        while n % p == 0:
            result[p] = result.get(p, 0) + 1
            n //= p
        p += 1
    if n > 1:
        result[n] = result.get(n, 0) + 1
    return result


def mu(n):
    fs = factor(n)
    return 0 if any(e > 1 for e in fs.values()) else (-1) ** len(fs)


def divisors(n):
    out = [1]
    for p, e in factor(n).items():
        out = [d * p ** j for d in out for j in range(e + 1)]
    return out


def crt_density_check():
    primes = (2, 3, 5)
    cases = classes = 0
    zero_cases = 0
    for q in (1, 2, 3, 4, 6, 8, 9, 12, 15, 18, 25, 27, 36, 45, 50, 60):
        modulus = math.lcm(q, math.prod(p * p for p in primes))
        units = [u for u in range(modulus) if math.gcd(u, modulus) == 1]
        denominators = Counter(u % q for u in units)
        for h in range(-12, 13):
            if h == 0:
                continue
            for eps in (-1, 1):
                counts = Counter(u % q for u in units
                                 if all((eps*u+h) % (p*p) for p in primes))
                classes += len(units)
                for a, denominator in denominators.items():
                    predicted = F(1)
                    for p in primes:
                        if q % p:
                            if h % p:
                                predicted *= 1 - F(1, p*(p-1))
                        elif q % (p*p):
                            if (eps*a+h) % p == 0:
                                predicted *= 1 - F(1, p)
                        elif (eps*a+h) % (p*p) == 0:
                            predicted = F(0)
                    actual = F(counts[a], denominator)
                    assert actual == predicted, (q, a, h, eps, actual, predicted)
                    zero_cases += predicted == 0
                    cases += 1
    return {"local_primes": primes, "parameter_cases": cases,
            "unit_class_visits": classes, "forced_zero_cases": zero_cases}


def nonunit_class_check():
    identities = reduced_checks = 0
    for q in range(1, 61):
        for t in range(1, 601):
            c = t % q
            v = math.gcd(c, q)
            qp = q // v
            t1 = t // v
            assert math.gcd(c // v, qp) == 1
            b_values = [b for b in divisors(t1) if all(v % p == 0 for p in factor(b))]
            rhs = mu(v) * sum(mu(t1 // b) for b in b_values)
            assert rhs == mu(t), (q, t, v, rhs)
            identities += 1
            for m in (1, 2, 3, 4, 5, 6, 10, 12, 15, 30):
                if math.gcd(t, m) != 1:
                    continue
                assert math.gcd(v, m) == 1
                for b in b_values:
                    assert math.gcd(b, m*qp) == 1
                    t2 = t1 // b
                    assert math.gcd(t2, math.lcm(m, qp)) == 1
                    assert (t2-(t % m)*pow(v*b, -1, m)) % m == 0
                    assert (t2-(c//v)*pow(b, -1, qp)) % qp == 0
                    reduced_checks += 1
    for qp in range(1, 61):
        fibers = defaultdict(list)
        for m in range(1, 501):
            fibers[math.lcm(m, qp)].append(m)
        assert max(map(len, fibers.values())) <= len(divisors(qp))
    return {"mobius_identities": identities, "reduced_crt_checks": reduced_checks,
            "lcm_fiber_moduli": 60}


def odd_mark_count_check():
    receipts = []
    for bands in (((7, 11),), ((3, 5), (7, 11), (13, 17))):
        K = len(bands)
        all_primes = tuple(itertools.chain.from_iterable(bands))
        selected = [math.prod(v) for v in itertools.product(*bands)]
        normalization = math.prod(sum((F(1, p) for p in b), F(0)) for b in bands)
        overlaps = 0
        for n in range(1, 10001):
            counts = [sum(n % p == 0 for p in b) for b in bands]
            W = math.prod(F(k, 2**(k-1)) if k else F(0) for k in counts) / normalization
            rhs = F(0)
            for a in selected:
                if n % a:
                    continue
                ell = n // a
                if math.gcd(a, ell) > 1:
                    overlaps += 1
                    continue
                damping = F(1, 2 ** sum(ell % p == 0 for p in all_primes))
                rhs += (-1)**K * mu(ell)*damping/normalization
            assert mu(n)*W == rhs, (K, n, W, rhs)
        receipts.append({"K": K, "positive_integers": 10000, "overlap_terms": overlaps})
    return receipts


def main():
    start = time.monotonic()
    result = {"status": "PASS_FINITE_IDENTITIES_ONLY",
              "crt_density": crt_density_check(),
              "nonunit_classes": nonunit_class_check(),
              "odd_mark_counts": odd_mark_count_check(),
              "asymptotic_claims_verified": False}
    result["elapsed_seconds"] = time.monotonic() - start
    Path("PROGRESSION_IDENTITY_CHECK.json").write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(result))


if __name__ == "__main__":
    import contextlib
    import io
    import os
    os.chdir(Path(__file__).resolve().parent)
    with contextlib.redirect_stdout(io.StringIO()):
        main()
    receipt = json.loads(Path('PROGRESSION_IDENTITY_CHECK.json').read_text())
    print('check_progression_identities' + " " + receipt["status"] + "; finite identities only")
