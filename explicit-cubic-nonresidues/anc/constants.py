# constants.py -- the numerical constants of the paper and the final inequalities of Theorems 1 and 2.
# Prints one summary line; -v prints every quantity.
import sys
import mpmath as mp
from sympy import primerange

mp.mp.dps = 30
V = '-v' in sys.argv
ok = True
notes = []


def chk(cond, text):
    global ok
    if not cond:
        ok = False
        notes.append('FAIL: ' + text)
    if V:
        print(('ok   ' if cond else 'FAIL ') + text)


# -- Section 2: -zeta_F'/zeta_F(2) = -zeta'/zeta(2) - L'/L(2, chi_{-3})
z = -mp.zeta(2, derivative=1) / mp.zeta(2)
chi = [0, 1, -1]
lc = -mp.dirichlet(2, chi, derivative=1) / mp.dirichlet(2, chi)
c2 = z + lc
# cross-check: sum_a Lambda(a) Na^{-2} over prime ideals of norm < 4e10 (closed forms for the geometric series)
S = mp.mpf(0)
for p in primerange(2, 200000):
    lp = mp.log(p)
    if p == 3:
        S += lp / 8                      # lambda: norm 3, sum_k 3^{-2k} = 1/8
    elif p % 3 == 1:
        S += 2 * lp / (p * p - 1)        # two primes of norm p
    else:
        S += 2 * lp / (p ** 4 - 1)       # inert: norm p^2, Lambda = 2 log p
chk(c2 <= mp.mpf('0.3974') and abs(c2 - S) < 1e-4, f"-zeta_F'/zeta_F(2) = {mp.nstr(c2, 8)} (prime-ideal sum {mp.nstr(S, 8)}) <= 0.3974")
l2p = mp.log(2 * mp.pi)
chk(l2p <= mp.mpf('1.83788'), f"log 2pi = {mp.nstr(l2p, 8)}")

# -- Lemma 2 constants
cL2 = -l2p + mp.mpf(1) / 48 + mp.mpf('0.3974')
chk(cL2 <= -1.4, f"Lemma 2: -log 2pi + 1/48 + 0.3974 = {mp.nstr(cL2, 8)} <= -1.4")
cF = mp.mpf('0.3974') + mp.log(3) / 2 - l2p + mp.mpf(1) / 48 + mp.mpf(3) / 2
chk(cF <= 0.63, f"Lemma 2 (zeta_F): 0.3974 + (1/2)log 3 - log 2pi + 1/48 + 3/2 = {mp.nstr(cF, 8)} <= 0.63")
chk(mp.log(9) / 2 + mp.log(2) - 1.4 > 0.39, f"ell(t) >= (1/2)log 9 + log 2 - 1.4 = {mp.nstr(mp.log(9)/2 + mp.log(2) - 1.4, 5)} > 0")

# -- Lemma 3 constants
near = mp.mpf(17) / 16 * 16 * mp.mpf(8) / 9
K = mp.mpf('2.5') * near + 5 * mp.mpf(17) / 16
chk(near <= 15.12 and K <= 43.12, f"Lemma 3: near-zero term 17/16*16*8/9 = {mp.nstr(near, 6)} <= 15.12; 2.5*15.12 + 5*17/16 = {mp.nstr(2.5*15.12 + 5*17/16., 6)} <= 43.12")
b1 = (0.4 + 2.2 + 1.85 - 43.12 * 1.4)
chk(43.12 / 2 <= 22 and 2 + 43.12 <= 46 and b1 < 0, f"(B1): coefficients {43.12/2}, {2 + 43.12}, constant {b1:.3f} < 0")
b2 = 2 * l2p + 18.12 + 2.2
chk(b2 <= 24, f"(B2): 2 log 2pi + 18.12 + 2.2 = {mp.nstr(b2, 6)} <= 24")
b1F = 0.4 + (mp.mpf(16) / 15 + 0.5 + 16 + 1) + 4.05 + 43.12 * 0.63
chk(b1F <= 51 and 2 + 43.12 <= 46, f"(B1_F): 0.4 + 18.567 + 4.05 + 43.12*0.63 = {mp.nstr(b1F, 6)} <= 51")
b2F = mp.log(3) + 2 * l2p + 18.12 + 2.2 + 51
chk(b2F <= 77, f"(B2_F): log 3 + 2 log 2pi + 18.12 + 2.2 + 51 = {mp.nstr(b2F, 6)} <= 77")

# -- (C1), (C2)
chk(mp.mpf(64) / 9 < mp.mpf(36) / 5, "(C1): 64/9 < 36/5")
off = 36 * (mp.log(2) - 1.4)
chk(off < 0, f"(C1): 36 ell(0) = 18 log(3Nf) + {mp.nstr(off, 6)}")
offF = 36 * (mp.log(2) + 0.63)
chk(offF <= 48, f"(C1) zeta_F: 36 ell_F(0) = {mp.nstr(offF, 6)} <= 48")
f0 = lambda t: 1 / (abs(mp.mpc(1 / 16., t)) * abs(mp.mpc(17 / 16., t)))
f1 = lambda t: mp.log(abs(t) + 2) / (abs(mp.mpc(1 / 16., t)) * abs(mp.mpc(17 / 16., t)))
I0 = 2 * mp.quad(f0, [0, 0.01, 0.1, 1, 10, 100, mp.inf])
I1 = 2 * mp.quad(f1, [0, 0.01, 0.1, 1, 10, 100, mp.inf])
tp = 2 * mp.pi
c2a, c2b, c2c = 23 * I0 / tp, (48 * I1 + 24 * I0) / tp, (48 * I1 + 77 * I0) / tp
chk(c2a <= 30 and c2b <= 92 and c2c <= 159, f"(C2): I0 = {mp.nstr(I0, 8)}, I1 = {mp.nstr(I1, 8)}; 23 I0/2pi = {mp.nstr(c2a, 6)} <= 30, (48 I1 + 24 I0)/2pi = {mp.nstr(c2b, 6)} <= 92, (48 I1 + 77 I0)/2pi = {mp.nstr(c2c, 6)} <= 159")

# -- Theorem 1: ell = log(3 N m) >= log 9; y = 36 L + 100; x = y^8
chk(mp.log(9) > 2.197, f"log 9 = {mp.nstr(mp.log(9), 6)}")
chk(1 / mp.log(2) <= 1.45, f"1/log 2 = {mp.nstr(1/mp.log(2), 6)} <= 1.45")
chk(36 + 100 / mp.log(9) <= 82, f"36 + 100/log 9 = {mp.nstr(36 + 100/mp.log(9), 6)} <= 82")
chk(36 * mp.log(9) + 100 >= 179, f"y >= 36 log 9 + 100 = {mp.nstr(36*mp.log(9) + 100, 6)} >= 179")


def thm1_ratio(L):
    y = 36 * L + 100
    x = y ** 8
    rhs = (18 * L + 48) * x ** (mp.mpf(7) / 8) + (30 * L + 251) * x ** (mp.mpf(1) / 16) + mp.mpf('2.9') * L * mp.log(x)
    return (x / 2) / rhs


def thm2_ratio(L, h):
    y = h * (36 * L + 100)
    x = y ** 8
    rhs = h * ((18 * L + 48) * x ** (mp.mpf(7) / 8) + (30 * L + 251) * x ** (mp.mpf(1) / 16) + mp.mpf('2.9') * L * mp.log(x) + 2 * mp.sqrt(x) * mp.log(x))
    return (x / 2) / rhs


Ls = [mp.log(9)] + [mp.mpf('2.2') * mp.mpf('1.2') ** k for k in range(0, 80)]
r1 = min(thm1_ratio(L) for L in Ls)
r2 = min(thm2_ratio(L, h) for L in Ls[:40] for h in [1, 2, 3, 6, 10, 100, 10 ** 4, 10 ** 8])
chk(r1 > 1, f"Theorem 1: min over L in [log 9, 4e6] of (x/2)/RHS = {mp.nstr(r1, 12)} > 1")
chk(r2 > 1, f"Theorem 2: min over L, h <= 1e8 of (x/2)/RHS = {mp.nstr(r2, 12)} > 1")
# the normalised slack of Theorem 1: (30L+251) y^{-6.5} + 23.2 L log y y^{-7} at y = 179
y0 = mp.mpf(179)
L0 = (y0 - 100) / 36
sl = (30 * L0 + 251) * y0 ** mp.mpf('-6.5') + mp.mpf('23.2') * L0 * mp.log(y0) * y0 ** -7
chk(sl < 1e-9, f"Theorem 1 slack terms at y = 179: {mp.nstr(sl, 4)} < 1e-9")
sl2 = sl + 16 * mp.log(y0) / y0 ** 3
chk(sl2 < 1e-4, f"Theorem 2 slack terms at y = 179: {mp.nstr(sl2, 4)} < 1e-4")

# -- Corollary 4'
c0 = 36 * mp.log(243) + 100
chk(c0 < mp.mpf('297.76') and c0 > mp.mpf('297.75'), f"36 log 243 + 100 = {mp.nstr(c0, 10)} < 297.76")
c502 = 72 + mp.mpf('297.76') / mp.log(2)
chk(c502 <= 502, f"72 + 297.76/log 2 = {mp.nstr(c502, 8)} <= 502")

# -- exponents 1/(1-theta) for the smaller boundaries quoted in Section 12 (not used in any proof)
sig_dag = mp.mpf('0.8749570194')
B_flat = mp.mpf('0.874886647039964')
e1, e2 = 1 / (1 - sig_dag), 1 / (1 - B_flat)
if V:
    print(f"exponent 1/(1-theta): theta = 7/8 -> 8; theta = {sig_dag} -> {mp.nstr(e1, 6)}; theta = {B_flat} -> {mp.nstr(e2, 6)}")

print(f"constants: {'OK' if ok else 'FAIL'}; -zeta_F'/zeta_F(2)={mp.nstr(c2, 7)}; I0={mp.nstr(I0, 7)}, I1={mp.nstr(I1, 7)}; (C2) coefficients {mp.nstr(c2a, 5)}/{mp.nstr(c2b, 5)}/{mp.nstr(c2c, 5)}; 36+100/log9={mp.nstr(36 + 100/mp.log(9), 5)}; 36log243+100={mp.nstr(c0, 8)}; Thm1 min ratio={mp.nstr(r1, 10)}; Thm2 min ratio={mp.nstr(r2, 8)}; exponents for sigma_dagger, B_flat: {mp.nstr(e1, 5)}, {mp.nstr(e2, 5)}" + ('; ' + '; '.join(notes) if notes else ''))
