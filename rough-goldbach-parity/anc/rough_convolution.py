"""Finite check of the identity lambda R_z = lambda * g_z, including prime powers."""
import json

limit = 500
least = list(range(limit + 1))
for p in range(2, limit + 1):
    if least[p] == p:
        for n in range(p * p, limit + 1, p):
            if least[n] == n:
                least[n] = p

def factor(n):
    result = {}
    while n > 1:
        p = least[n]
        result[p] = result.get(p, 0) + 1
        n //= p
    return result

def lam(n):
    return (-1) ** sum(factor(n).values())

checks = 0
for z in (2, 3, 5, 7, 11):
    for n in range(1, limit + 1):
        actual = 0
        for d in range(1, n + 1):
            if n % d:
                continue
            fac = factor(d)
            if all(k == 1 for k in fac.values()) and all(p <= z for p in fac):
                actual += lam(n // d)
        expected = lam(n) if all(p > z for p in factor(n)) else 0
        assert actual == expected, (z, n, actual, expected)
        checks += 1

summary = {
    "status": "PASS",
    "exact_checks": checks,
    "identity": "lambda R_z = lambda * (mu^2 1_{P^+ <= z})",
}
print(json.dumps(summary))
