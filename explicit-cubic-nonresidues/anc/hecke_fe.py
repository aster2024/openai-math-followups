# hecke_fe.py -- the gamma-factor check of Section 11: the functional equation of L(s, chi_2) with archimedean factor
# Gamma_C(s) = 2 (2 pi)^{-s} Gamma(s) and conductor D = 3 N f = 108 is equivalent to theta(1/y) = W y theta(y),
# theta(y) = sum a_n exp(-2 pi n y / sqrt D).  Tested at four values of y, also with wrong D.
# Prints one summary line; -v prints each D.
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import mpmath as mp  # noqa: E402
from hecke_chi2 import coeffs  # noqa: E402

V = '-v' in sys.argv
mp.mp.dps = 30
a = coeffs()


def theta(y, D):
    c = 2 * mp.pi * y / mp.sqrt(D)
    return mp.fsum(a[n] * mp.exp(-c * n) for n in range(1, len(a)))


ys = [mp.mpf('1.1'), mp.mpf('1.3'), mp.mpf('0.95'), mp.mpf('1.7')]
dev = {}
for D in [108, 36, 27, 324, 12]:
    r = [theta(1 / y, D) / (y * theta(y, D)) for y in ys]
    dev[D] = max(abs(x - 1) for x in r)
    if V:
        print(f"D={D}: theta(1/y)/(y theta(y)) at y=1.1,1.3,0.95,1.7: {[mp.nstr(x, 12) for x in r]}")
ok = dev[108] < 1e-25 and all(dev[D] > 0.01 for D in [36, 27, 324, 12])
print(f"hecke_fe: {'OK' if ok else 'FAIL'}; a_n of L(s,chi_2) for n <= 400; theta(1/y) = y theta(y) holds with D = 108 (W = 1) to {mp.nstr(dev[108], 2)} at y = 1.1, 1.3, 0.95, 1.7, and fails for D = 36, 27, 324, 12 (deviations {', '.join(mp.nstr(dev[D], 2) for D in [36, 27, 324, 12])})")
