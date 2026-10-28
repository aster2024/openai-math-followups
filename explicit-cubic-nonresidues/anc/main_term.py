# main_term.py -- S_1(x) = sum_a Lambda(a) (1 - Na/x)_+ over the nonzero ideals of Z[w], computed from a prime sieve,
# against the main term x/2 of Lemma 6.1 and the lower bound of Proposition 6.4.  Prints one summary line; -v prints each x.
import math
import sys

import numpy as np

V = '-v' in sys.argv
XMAX = 10 ** 7
sieve = np.ones(XMAX + 1, dtype=bool)
sieve[:2] = False
for i in range(2, int(XMAX ** 0.5) + 1):
    if sieve[i]:
        sieve[i * i::i] = False
primes = np.nonzero(sieve)[0]
ok = True
rows = []
for x in [10 ** 4, 10 ** 5, 10 ** 6, 10 ** 7]:
    S = 0.0
    for p in primes[primes < x]:
        p = int(p)
        lp = math.log(p)
        if p == 3:
            q = 3
            while q < x:
                S += lp * (1 - q / x)
                q *= 3
        elif p % 3 == 1:            # two primes of norm p
            q = p
            while q < x:
                S += 2 * lp * (1 - q / x)
                q *= p
        else:                       # inert: one prime of norm p^2, Lambda = 2 log p
            q = p * p
            while q < x:
                S += 2 * lp * (1 - q / x)
                q *= p * p
    lower = x / 2 - 48 * x ** (7 / 8) - 159 * x ** (1 / 16)
    rows.append((x, S / (x / 2), S >= lower))
    ok = ok and S >= lower
    if V:
        print(f"x = {x:.0e}: S_1(x)/(x/2) = {S/(x/2):.6f}; Prop. 6.4 lower bound / (x/2) = {lower/(x/2):.4f}")
print(f"main_term: {'OK' if ok else 'FAIL'}; S_1(x)/(x/2) = " + ', '.join(f"{r:.6f} (x=1e{int(math.log10(x))})" for x, r, _ in rows) + "; Proposition 6.4 holds at these x")
