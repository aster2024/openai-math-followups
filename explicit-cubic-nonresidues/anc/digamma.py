# digamma.py -- Lemma 3.1 (digamma bounds) on dense grids, and a spot check of Binet's second formula.
# Prints one summary line; -v prints each case.
import sys
import numpy as np
from scipy.special import digamma
import mpmath as mp

V = '-v' in sys.argv
t = np.concatenate([np.arange(0, 10, 0.005), np.arange(10, 110, 0.05), np.arange(110, 2010, 0.5)])
lg = np.log(t + 2)
cases = []  # (name, slack)


def case(name, values, bound):
    slack = float(np.min(bound - values))
    cases.append((name, slack))
    if V:
        print(f"{name}: min slack = {slack:.4f}")


psi2 = digamma(2 + 1j * t)
case("(a) Re psi(2+it) <= log(t+2) + 1/48", psi2.real, lg + 1 / 48)
case("(a) |psi(2+it)| <= log(t+2) + 1.85", np.abs(psi2), lg + 1.85)
case("(b) |psi(15/16+it)| <= log(t+2) + 2.2", np.abs(digamma(15 / 16 + 1j * t)), lg + 2.2)
case("(b) |psi(17/16+it)| <= log(t+2) + 2.12", np.abs(digamma(17 / 16 + 1j * t)), lg + 2.12)
case("(c) |psi(1/16+it)| <= log(t+2) + 18.12", np.abs(digamma(1 / 16 + 1j * t)), lg + 18.12)
# (d): 1/16 <= sigma <= 2, |psi(sigma+it)| <= log(t+2) + 1/sigma + 2.2
worst = None
for s in np.arange(1 / 16, 2 + 1e-9, 1 / 64):
    v = np.abs(digamma(s + 1j * t))
    sl = float(np.min(lg + 1 / s + 2.2 - v))
    if worst is None or sl < worst[0]:
        worst = (sl, s)
cases.append(("(d) strip", worst[0]))
if V:
    print(f"(d) |psi(sigma+it)| <= log(t+2) + 1/sigma + 2.2 on 1/16 <= sigma <= 2: min slack = {worst[0]:.4f} at sigma = {worst[1]:.4f}")

# Binet's second formula (DLMF 5.9.13) at five points, and int_0^inf t/(e^{2 pi t}-1) dt = 1/24
mp.mp.dps = 25
err = 0
for z in [mp.mpf(2), mp.mpc(2, 1), mp.mpc(2, 10), mp.mpc(0.5, 3), mp.mpc(1, -7), mp.mpc(1 / 16., 0.3)]:
    rhs = mp.log(z) - 1 / (2 * z) - 2 * mp.quad(lambda u: u / ((u * u + z * z) * (mp.exp(2 * mp.pi * u) - 1)), [0, 1, 10, mp.inf])
    err = max(err, abs(mp.digamma(z) - rhs))
e24 = abs(mp.quad(lambda u: u / (mp.exp(2 * mp.pi * u) - 1), [0, 1, 10, mp.inf]) - mp.mpf(1) / 24)
binet_ok = err < 1e-18 and e24 < 1e-18
if V:
    print(f"Binet: max error {mp.nstr(err, 3)}; integral - 1/24 = {mp.nstr(e24, 3)}")
ok = all(s > 0 for _, s in cases) and binet_ok
print(f"digamma: {'OK' if ok else 'FAIL'}; grid t in [0, 2010] ({len(t)} points), min slack per case: " + ', '.join(f"{n.split(')')[0]}) {s:.3f}" for n, s in cases) + f"; Binet formula max error {mp.nstr(err, 2)}")
