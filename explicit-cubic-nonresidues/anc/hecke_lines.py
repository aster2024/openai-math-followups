# hecke_lines.py -- L'/L(s, chi_2) on Re s = 15/16 and Re s = 1/16 against (B1), (B2) of Lemma 5.1 with
# log(3 N f) = log 108, computed from the incomplete-gamma expansion of Lambda(s) (W = 1 from hecke_fe.py).
# Prints one summary line; -v prints each height.
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import mpmath as mp  # noqa: E402
from hecke_chi2 import coeffs  # noqa: E402

V = '-v' in sys.argv
mp.mp.dps = 35
D = mp.mpf(108)
sq = mp.sqrt(D)
a = coeffs(220)
nz = [n for n in range(1, len(a)) if a[n] != 0]
x0 = 2 * mp.pi / sq
A = sq / (2 * mp.pi)


def Lam(s):
    return mp.fsum(a[n] * ((A / n) ** s * mp.gammainc(s, x0 * n) + (A / n) ** (1 - s) * mp.gammainc(1 - s, x0 * n)) for n in nz)


def Lfun(s):
    return Lam(s) / (A ** s * mp.gamma(s))


def logder(s, h=mp.mpf('1e-12')):
    return (Lfun(s + h) - Lfun(s - h)) / (2 * h * Lfun(s))


T0 = time.time()
big = coeffs(3000)
maxdiff = 0
for s in [mp.mpf(2), mp.mpc(1.5, 3)]:
    ds = mp.fsum(big[n] * mp.mpf(n) ** (-s) for n in range(1, 3001) if big[n] != 0)
    maxdiff = max(maxdiff, abs(Lfun(s) - ds))
    if V:
        print(f"L({s}): expansion {mp.nstr(Lfun(s), 10)}, Dirichlet series to 3000: {mp.nstr(ds, 10)}")
L3 = mp.log(108)
w1 = w2 = 0
v2_at_0 = None
for t in [0, 1, 2, 3, 5, 8, 10, 12, 15, 18]:
    v1 = abs(logder(mp.mpc(mp.mpf(15) / 16, t)))
    v2 = abs(logder(mp.mpc(mp.mpf(1) / 16, t)))
    if t == 0:
        v2_at_0 = v2
    b1 = 22 * L3 + 46 * mp.log(t + 2)
    b2 = 23 * L3 + 48 * mp.log(t + 2) + 24
    w1 = max(w1, v1 / b1)
    w2 = max(w2, v2 / b2)
    if V:
        print(f"t={t:5.1f}  |L'/L(15/16+it)|={mp.nstr(v1, 5):>9} (B1 bound {mp.nstr(b1, 5)})   |L'/L(1/16+it)|={mp.nstr(v2, 5):>9} (B2 bound {mp.nstr(b2, 5)})")
ok = maxdiff < 1e-4 and w1 < 1 and w2 < 1
print(f"hecke_lines: {'OK' if ok else 'FAIL'}; chi_2 (D = 108): expansion agrees with the Dirichlet series to {mp.nstr(maxdiff, 2)}; at t = 0,1,2,3,5,8,10,12,15,18 |L'/L| is at most {mp.nstr(100*w1, 3)}% of (B1) on Re s = 15/16 and {mp.nstr(100*w2, 3)}% of (B2) on Re s = 1/16 (|L'/L(1/16)| = {mp.nstr(v2_at_0, 4)}, close to 16 = 1/(1/16) from the trivial zero at 0); {time.time()-T0:.1f} s")
