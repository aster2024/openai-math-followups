# zetaF.py -- Dedekind zeta function of F = Q(sqrt-3), zeta_F = zeta * L(., chi_{-3}):
# (a) |zeta_F'/zeta_F| on Re s = 15/16 and 1/16 against (B1_F), (B2_F) of Lemma 5.1;
# (b) zero counts #{rho : |gamma - t| <= 1} against Lemma 4.1(b) for zeta_F: (5/2)(log(|t|+2) + 0.63).
# Prints one summary line; -v prints details.
import sys
import time

import mpmath as mp

mp.mp.dps = 15
V = '-v' in sys.argv
chi = [0, 1, -1]


def ld(s):
    return mp.zeta(s, derivative=1) / mp.zeta(s) + mp.dirichlet(s, chi, 1) / mp.dirichlet(s, chi)


T0 = time.time()
worst1 = (-1e9, None)
worst2 = (-1e9, None)
t = 0.0
while t <= 40:
    v1 = abs(ld(mp.mpc(15 / 16., t)))
    b1 = 46 * mp.log(t + 2) + 51
    v2 = abs(ld(mp.mpc(1 / 16., t)))
    b2 = 48 * mp.log(t + 2) + 77
    if v1 / b1 > worst1[0]:
        worst1 = (v1 / b1, t, v1)
    if v2 / b2 > worst2[0]:
        worst2 = (v2 / b2, t, v2)
    t += 0.25
if V:
    print(f"(B1_F) max |zF'/zF(15/16+it)| / (46 log(t+2)+51), t in [0,40] step 0.25: {mp.nstr(worst1[0], 5)} at t={worst1[1]:.2f} (value {mp.nstr(worst1[2], 5)})")
    print(f"(B2_F) max |zF'/zF(1/16+it)| / (48 log(t+2)+77), t in [0,40] step 0.25: {mp.nstr(worst2[0], 5)} at t={worst2[1]:.2f} (value {mp.nstr(worst2[2], 5)})")
# zeros of zeta up to height 42
zz = []
n = 1
while True:
    g = float(mp.im(mp.zetazero(n)))
    if g > 42:
        break
    zz.append(g)
    n += 1


# zeros of L(s, chi_-3) via the Hardy-type function (chi_-3 odd, real, root number 1)
def Z(t):
    th = (t / 2) * mp.log(3 / mp.pi) + mp.im(mp.loggamma(mp.mpf(3) / 4 + 1j * t / 2))
    return mp.re(mp.exp(1j * th) * mp.dirichlet(mp.mpc(0.5, t), chi))


zl = []
prev = Z(0.01)
tt = 0.01
while tt < 42:
    tn = tt + 0.05
    cur = Z(tn)
    if prev * cur < 0:
        zl.append(float(mp.findroot(Z, (tt, tn), solver='anderson')))
    prev, tt = cur, tn
allg = zz + zl
allg = allg + [-g for g in allg]
worst = (-1e9, None)
for k in range(0, 401):
    t = k * 0.1
    cnt = sum(1 for g in allg if abs(g - t) <= 1)
    bd = 2.5 * (mp.log(t + 2) + 0.63)
    if cnt - bd > worst[0]:
        worst = (cnt - bd, t, cnt, bd)
if V:
    print(f"zeta zeros <= 42: {len(zz)}; L(chi_-3) zeros <= 42: {len(zl)}, first few: {[round(x, 3) for x in zl[:4]]}")
    print(f"Lemma 4.1(b) for zeta_F, t in [0,40]: max (count - bound) = {mp.nstr(worst[0], 4)} at t={worst[1]:.1f} (count {worst[2]}, bound {mp.nstr(worst[3], 4)})")
ok = worst1[0] < 1 and worst2[0] < 1 and worst[0] < 0
print(f"zetaF: {'OK' if ok else 'FAIL'}; t in [0,40]: |zeta_F'/zeta_F| is at most {mp.nstr(100*worst1[0], 3)}% of (B1_F) on Re s=15/16 and {mp.nstr(100*worst2[0], 3)}% of (B2_F) on Re s=1/16; zero count in |gamma-t|<=1 (zeros of zeta and L(chi_-3) to height 42: {len(zz)}+{len(zl)}) stays >= {mp.nstr(-worst[0], 3)} below the bound of Lemma 4.1(b); {time.time()-T0:.1f} s")
