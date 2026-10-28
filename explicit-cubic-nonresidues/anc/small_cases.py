# small_cases.py -- Corollary 4': least prime p = 1 (mod 3) with a a cubic non-residue, for 2 <= a <= 20000 (non-cubes),
# against the bound (36 log(243 a^2) + 100)^8; the inert-prime remark; the prime-ideal version of Theorem 4.
# Prints one summary line; -v prints the tables of Section 11.
import math
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from sympy import primerange, integer_nthroot  # noqa: E402
from zw import cubic_symbol, prime_elements, norm  # noqa: E402

V = '-v' in sys.argv
P1 = [p for p in primerange(2, 10 ** 5) if p % 3 == 1]


def is_cube(a):
    return integer_nthroot(abs(a), 3)[1]


def least_p(a):
    for p in P1:
        if a % p == 0:
            continue
        if pow(a % p, (p - 1) // 3, p) != 1:
            return p
    return None


AMAX = 20000
worst = (0, None)
champions = []
table = {}
ok = True
for a in range(2, AMAX + 1):
    if is_cube(a):
        continue
    p = least_p(a)
    table[a] = p
    bound = (36 * math.log(243 * a * a) + 100) ** 8
    if not (p is not None and p < bound):
        ok = False
    if p > worst[0]:
        worst = (p, a)
        champions.append((a, p))
# negative a: -a is a cube mod p iff a is (since -1 = (-1)^3), so least_p(-a) = least_p(a); spot check
for a in [-2, -3, -5, -6, -7, -10, -2478]:
    if least_p(a) != least_p(-a):
        ok = False
# inert primes never give a non-residue for rational a (Remark 9.3(i))
viol = 0
for l in primerange(5, 400):
    if l % 3 != 2:
        continue
    for a in range(2, 300):
        if a % l == 0:
            continue
        if cubic_symbol((a, 0), (l, 0)) != 0:
            viol += 1
ok = ok and viol == 0
# Theorem 4 as stated (prime ideals): least norm of a prime ideal p not dividing 3a with (a/p)_3 != 1
PR = sorted(prime_elements(5000), key=norm)
ideal_rows = []
for a in [2, 3, 5, 6, 7, 10]:
    for p in PR:
        if norm(p) % 3 == 0 or math.gcd(norm(p), a) != 1:
            continue
        if cubic_symbol((a, 0), p) != 0:
            ideal_rows.append((a, norm(p)))
            break
    if ideal_rows[-1][1] != table[a]:
        ok = False
if V:
    print("least p = 1 (mod 3) with a not a cube mod p, 2 <= a <= 40 (cubes omitted):")
    print("  " + ", ".join(f"{a}:{table[a]}" for a in range(2, 41) if a in table))
    print("records (a, least p) for 2 <= a <= 20000:")
    print("  " + ", ".join(f"({a}, {p})" for a, p in champions))
    print("prime-ideal version (a, least norm):", ideal_rows)
    print(f"inert-prime violations (l = 2 mod 3, 5 <= l < 400, 2 <= a < 300): {viol}")
print(f"small_cases: {'OK' if ok else 'FAIL'}; 2 <= a <= {AMAX} non-cubes: least p < (36 log(243 a^2)+100)^8 always; max least p = {worst[0]} at a = {worst[1]} (bound there {(36*math.log(243*worst[1]**2)+100)**8:.2e}); records {champions}; least p for a=2,3,5,10 is 7 and for a=6,7 is 13; inert-prime violations {viol}; prime-ideal least norms agree with least p")
