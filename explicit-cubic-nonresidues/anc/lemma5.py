# lemma5.py -- Lemma 9.2: psi_pi(a) = (alpha_1(a)/pi)_3 is a well defined character of Cl_{3 pi} of order exactly 3;
# and the lambda-part of its conductor (Remark 9.4).  Prints one summary line; -v prints each prime.
import os
import random
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from zw import *  # noqa: E402
from sympy import isprime  # noqa: E402

V = '-v' in sys.argv
random.seed(1)


def is_prime_elt(p):
    n = norm(p)
    if isprime(n):
        return True
    r = int(round(n ** 0.5))
    return r * r == n and isprime(r) and r % 3 == 2


pis = [p for p in [(3, 1), (4, 1), (2, 0), (5, 0), (7, 3), (6, 1), (11, 0), (9, 1)] if norm(p) % 3 == 1 and is_prime_elt(p)]
PR = prime_elements(30000)
tot_trials = 0
tot_bad = 0
all_three = True
cond_ok = True
rows = []
for pi in pis:
    m = mul((3, 0), pi)

    def psi(a):
        return cubic_symbol(one_primary(a), pi)

    bad = 0
    vals = set()
    trials = 0
    for _ in range(3000):
        a = (random.randint(-200, 200), random.randint(-200, 200))
        if gcd(norm(a), 3 * norm(pi)) != 1:
            continue
        trials += 1
        v = psi(a)
        vals.add(v)
        # well-definedness on ray classes mod 3 pi: b = u a + m c lies in the same ray class
        u = random.choice(UNITS)
        c = (random.randint(-50, 50), random.randint(-50, 50))
        b = add(mul(u, a), mul(m, c))
        if gcd(norm(b), 3 * norm(pi)) == 1 and psi(b) != v:
            bad += 1
        # multiplicativity
        a2 = (random.randint(-200, 200), random.randint(-200, 200))
        if gcd(norm(a2), 3 * norm(pi)) == 1 and psi(mul(a, a2)) != (v + psi(a2)) % 3:
            bad += 1
    tot_trials += trials
    tot_bad += bad
    all_three = all_three and vals == {0, 1, 2}
    # lambda-part of the conductor: least k with psi_pi constant on ray classes mod lambda^k pi
    res = []
    for k in range(0, 4):
        mk = pi
        for _ in range(k):
            mk = mul(mk, LAM)
        R = IdealMod(mk)
        seen = {}
        consistent = True
        for p in PR:
            if norm(p) % 3 == 0 or divides(pi, p):
                continue
            v = cubic_symbol(one_primary(p), pi)
            key = min(R.red(mul(u, p)) for u in UNITS)
            if key in seen and seen[key] != v:
                consistent = False
                break
            seen[key] = v
        res.append(consistent)
    kmin = min(k for k in range(4) if res[k])
    expected = 0 if norm(pi) % 9 == 1 else 2
    cond_ok = cond_ok and kmin == expected
    rows.append((pi, norm(pi), norm(pi) % 9, trials, bad, sorted(vals), kmin))
    if V:
        print(f"pi={pi} N={norm(pi)} N mod 9={norm(pi) % 9}: trials={trials} violations={bad} values={sorted(vals)} lambda-exponent of conductor={kmin} (expected {expected})")
# Remark 9.4: pi = (19, omega - 7) = (5 + 2 omega) has N(pi) = 19 = 1 (mod 9) but (lambda/pi)_3 != 1
pi19 = (5, 2)
rem94 = norm(pi19) == 19 and divides(pi19, (-7, 1)) and cubic_symbol(LAM, pi19) == 2
if V:
    print(f"Remark 9.4: pi = 5 + 2w, N = {norm(pi19)}, divides omega - 7: {divides(pi19, (-7, 1))}, (lambda/pi)_3 = w^{cubic_symbol(LAM, pi19)}")
ok = tot_bad == 0 and all_three and cond_ok and rem94
print(f"lemma5: {'OK' if ok else 'FAIL'}; primes pi of norms {[norm(p) for p in pis]}: {tot_trials} random checks of well-definedness and multiplicativity, {tot_bad} violations; all three values taken: {all_three}; lambda-exponent of the conductor = 2 when N(pi) != 1 (mod 9) and 0 when N(pi) = 1 (mod 9): {cond_ok}; Remark 9.4 example pi = 5+2w = (19, w-7): (lambda/pi)_3 = w^2 != 1: {rem94}")
