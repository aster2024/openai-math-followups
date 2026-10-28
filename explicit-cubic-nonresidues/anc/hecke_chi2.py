# hecke_chi2.py -- Dirichlet coefficients of L(s, chi_2), chi_2(p) = (2/p)_3, the Artin character of F(2^{1/3})/F,
# F = Q(sqrt-3).  Conductor f = (6) (lambda-exponent 2, (2)-exponent 1; see kummer_conductor.py), N f = 36,
# analytic conductor D = |d_F| N f = 108.  Library used by hecke_fe.py, hecke_lines.py, hecke_zeros.py.
import mpmath as mp
from sympy import primerange, factorint

NMAX = 400


def coeffs(nmax=NMAX):
    """a_n = sum over ideals of norm n of chi_2(ideal), n <= nmax"""
    w = mp.exp(2j * mp.pi / 3)
    a = [mp.mpc(0)] * (nmax + 1)
    a[1] = mp.mpc(1)
    pk = {}
    for p in primerange(2, nmax + 1):
        vals = []
        k = 0
        q = 1
        while q <= nmax:
            if p == 2 or p == 3:
                v = 1 if k == 0 else 0          # ramified in F(2^{1/3})/F: chi_2 = 0 there
            elif p % 3 == 2:
                v = 1 if k % 2 == 0 else 0      # inert: one prime of norm p^2, 2 is a cube mod it
            else:
                cube = pow(2, (p - 1) // 3, p) == 1
                x, y = (1, 1) if cube else (w, w ** 2)   # the two primes above p
                v = sum(x ** i * y ** (k - i) for i in range(k + 1))
            vals.append(v)
            k += 1
            q *= p
        pk[p] = vals
    for n in range(2, nmax + 1):
        v = mp.mpc(1)
        for p, e in factorint(n).items():
            v *= pk[p][e]
        a[n] = v
    return [mp.re(x) if abs(mp.im(x)) < 1e-20 else x for x in a]
