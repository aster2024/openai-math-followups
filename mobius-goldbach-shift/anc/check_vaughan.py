"""Exact finite check of the sifted Vaughan identity and both corrections.

Logarithms are represented by integer vectors indexed by primes, so no
floating-point identity is used. This checks finite algebra, not estimates.
"""
from collections import Counter
from math import isqrt


def factors(n):
    out = Counter()
    p = 2
    while p * p <= n:
        while n % p == 0:
            out[p] += 1
            n //= p
        p += 1
    if n > 1:
        out[n] += 1
    return out


LIMIT = 600
FACTOR = [Counter()] + [factors(n) for n in range(1, LIMIT + 1)]
MU = [0] + [0 if any(e > 1 for e in FACTOR[n].values())
             else (-1) ** len(FACTOR[n]) for n in range(1, LIMIT + 1)]
LAMBDA = [Counter()] + [Counter({next(iter(FACTOR[n])): 1})
                       if len(FACTOR[n]) == 1 else Counter()
                       for n in range(1, LIMIT + 1)]
DIVISORS = [[]] + [[d for d in range(1, isqrt(n) + 1) if n % d == 0]
                   for n in range(1, LIMIT + 1)]
for n in range(1, LIMIT + 1):
    DIVISORS[n] = sorted({d for a in DIVISORS[n] for d in (a, n // a)})


def add(out, vector, coefficient):
    for p, value in vector.items():
        out[p] += coefficient * value


def normalized(vector):
    return {p: e for p, e in vector.items() if e}


def rough(n, z):
    return all(p > z for p in FACTOR[n])


def main():
    identities = 0
    for u in (2, 5, 13):
        for v in (2, 7, 17):
            for n in range(1, LIMIT + 1):
                out = Counter()
                if n <= v:
                    add(out, LAMBDA[n], 1)
                for d in DIVISORS[n]:
                    k = n // d
                    if d <= u:
                        add(out, FACTOR[k], MU[d])
                        for ell in DIVISORS[k]:
                            if ell <= v:
                                add(out, LAMBDA[ell], -MU[d])
                    else:
                        for ell in DIVISORS[k]:
                            if ell > v:
                                add(out, LAMBDA[ell], MU[d])
                assert normalized(out) == normalized(LAMBDA[n])
                identities += 1

    corrections = 0
    for z in (2, 3, 5, 11):
        for y in (30, 75, 150, 250):
            for endpoint in (y + 1, y + y // 2, 2 * y):
                raw, sifted, primes = Counter(), Counter(), Counter()
                low_bases, all_powers = Counter(), Counter()
                for n in range(y + 1, endpoint + 1):
                    weight = n % 5 - 2
                    add(raw, LAMBDA[n], weight)
                    if rough(n, z):
                        add(sifted, LAMBDA[n], weight)
                    if len(FACTOR[n]) == 1:
                        p, exponent = next(iter(FACTOR[n].items()))
                        if exponent == 1:
                            add(primes, LAMBDA[n], weight)
                        if p <= z:
                            add(low_bases, LAMBDA[n], weight)
                        if exponent >= 2:
                            add(all_powers, LAMBDA[n], weight)
                diff1, diff2 = raw.copy(), raw.copy()
                add(diff1, sifted, -1)
                add(diff2, primes, -1)
                assert normalized(diff1) == normalized(low_bases)
                assert normalized(diff2) == normalized(all_powers)
                corrections += 1
    multiplicativity = 0
    for a in range(1, 25):
        for b in range(1, 25):
            for z in (2, 3, 5, 11):
                assert rough(a * b, z) == (rough(a, z) and rough(b, z))
                multiplicativity += 1
    print(f"check_vaughan PASS: convolution={identities}, corrections={corrections}, "
          f"sieve_products={multiplicativity}; finite algebra only")


if __name__ == "__main__":
    main()
