# hecke_zeros.py -- zeros of L(s, chi_2) on the critical line, t in [0, 16] (sign changes of the real function
# Lambda(1/2 + it)), against Lemma 4.1(b): #{|gamma - t| <= 1} <= (5/4) log 108 + (5/2) log(|t|+2) - 3.5.
# Zeros off the line would only be missed, so this is a sanity check of the size of the constant, not a proof.
# Prints one summary line; -v prints the zeros.
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import mpmath as mp  # noqa: E402
from hecke_chi2 import coeffs  # noqa: E402

V = '-v' in sys.argv
mp.mp.dps = 25
D = mp.mpf(108)
sq = mp.sqrt(D)
a = coeffs(160)
nz = [n for n in range(1, len(a)) if a[n] != 0]
x0 = 2 * mp.pi / sq
A = sq / (2 * mp.pi)


def Lam(s):
    return mp.fsum(a[n] * ((A / n) ** s * mp.gammainc(s, x0 * n) + (A / n) ** (1 - s) * mp.gammainc(1 - s, x0 * n)) for n in nz)


T0 = time.time()
zs = []
tt = 0.0
prev = mp.re(Lam(mp.mpc(0.5, tt)))
im = abs(mp.im(Lam(mp.mpc(0.5, 3.3))))
while tt < 16:
    tn = tt + 0.1
    cur = mp.re(Lam(mp.mpc(0.5, tn)))
    if prev * cur < 0:
        zs.append((tt + tn) / 2)
    prev, tt = cur, tn
allg = zs + [-z for z in zs]
worst = None
for k in range(0, 151):
    t = k * 0.1
    cnt = sum(1 for g in allg if abs(g - t) <= 1)
    bd = 1.25 * mp.log(108) + 2.5 * mp.log(t + 2) - 3.5
    if worst is None or cnt - bd > worst[0]:
        worst = (cnt - bd, t, cnt, bd)
if V:
    print(f"Lambda(1/2) = {mp.nstr(mp.re(Lam(mp.mpf(0.5))), 8)}; |Im Lambda(1/2+3.3i)| = {mp.nstr(im, 3)}")
    print(f"approximate ordinates in (0,16]: {[round(z, 2) for z in zs]}")
    print(f"max(count - bound) over t in [0,15] = {mp.nstr(worst[0], 4)} at t={worst[1]:.1f} (count {worst[2]}, bound {mp.nstr(worst[3], 4)})")
ok = im < 1e-15 and worst[0] < 0
print(f"hecke_zeros: {'OK' if ok else 'FAIL'}; {len(zs)} sign changes of Lambda(1/2+it, chi_2) in (0,16] (first {[round(z, 2) for z in zs[:4]]}); count in |gamma-t|<=1 stays >= {mp.nstr(-worst[0], 3)} below the bound of Lemma 4.1(b) for t in [0,15]; {time.time()-T0:.1f} s")
