# zw.py -- minimal arithmetic in Z[w], w = exp(2 pi i/3), w^2 = -1 - w.  Elements are pairs (x, y) = x + y w.
# Library used by lemma5.py, kummer_conductor.py and small_cases.py.  Not a script.
from math import gcd, isqrt


def mul(a, b):
    x1, y1 = a
    x2, y2 = b
    # (x1 + y1 w)(x2 + y2 w) = x1 x2 + (x1 y2 + x2 y1) w + y1 y2 w^2,  w^2 = -1 - w
    return (x1 * x2 - y1 * y2, x1 * y2 + x2 * y1 - y1 * y2)


def add(a, b):
    return (a[0] + b[0], a[1] + b[1])


def sub(a, b):
    return (a[0] - b[0], a[1] - b[1])


def norm(a):
    x, y = a
    return x * x - x * y + y * y


def conj(a):
    x, y = a
    return (x - y, -y)  # conj(w) = w^2 = -1 - w


W = (0, 1)
ONE = (1, 0)
UNITS = [(1, 0), (-1, 0), (0, 1), (0, -1), (-1, -1), (1, 1)]  # 1, -1, w, -w, w^2, -w^2
LAM = (1, -1)  # lambda = 1 - w, norm 3


def rdiv(n, d):
    """round(n/d) for integers, d > 0"""
    return (2 * n + d) // (2 * d)


def divround(a, b):
    """nearest lattice point to a/b"""
    nb = norm(b)
    num = mul(a, conj(b))
    return (rdiv(num[0], nb), rdiv(num[1], nb))


def modelt(a, b):
    q = divround(a, b)
    return sub(a, mul(b, q))


def divides(b, a):
    nb = norm(b)
    num = mul(a, conj(b))
    return num[0] % nb == 0 and num[1] % nb == 0


def powmod(a, e, m):
    r = ONE
    a = modelt(a, m)
    while e:
        if e & 1:
            r = modelt(mul(r, a), m)
        a = modelt(mul(a, a), m)
        e >>= 1
    return r


def egcd(a, b):
    if b == 0:
        return (a, 1, 0) if a >= 0 else (-a, -1, 0)
    g, s, t = egcd(b, a % b)
    return (g, t, s - (a // b) * t)


class IdealMod:
    """canonical reduction modulo the principal ideal mu*O (Hermite normal form of the lattice)"""

    def __init__(self, mu):
        self.mu = mu
        v1 = mu
        v2 = mul(mu, W)
        g, s, t = egcd(v1[1], v2[1])
        self.w = (s * v1[0] + t * v2[0], g)
        xu = (v2[1] // g) * v1[0] - (v1[1] // g) * v2[0]
        self.A = abs(xu)
        self.g = g
        assert self.A * self.g == norm(mu), (self.A, self.g, norm(mu))

    def red(self, a):
        x, y = a
        k = y // self.g
        x -= k * self.w[0]
        y -= k * self.g
        return (x % self.A, y)


def cubic_symbol(a, pi):
    """(a/pi)_3 as the exponent j in {0,1,2} with symbol = w^j; None if pi | a.  Requires N(pi) = 1 mod 3."""
    if divides(pi, a):
        return None
    n = norm(pi)
    r = powmod(a, (n - 1) // 3, pi)
    for j, z in enumerate([ONE, W, mul(W, W)]):
        if divides(pi, sub(r, z)):
            return j
    raise ValueError("not a cube root of unity", a, pi, r)


def one_primary(a):
    """the unique associate u*a with u*a = 1 mod 3 (a coprime to 3)"""
    three = (3, 0)
    res = []
    for u in UNITS:
        b = mul(u, a)
        if divides(three, sub(b, ONE)):
            res.append(b)
    assert len(res) == 1, (a, res)
    return res[0]


def prime_elements(maxnorm):
    """one generator for each prime ideal of norm <= maxnorm"""
    from sympy import primerange
    out = []
    for p in primerange(2, maxnorm + 1):
        if p == 3:
            out.append(LAM)
        elif p % 3 == 2:
            if p * p <= maxnorm:
                out.append((p, 0))
        else:
            # find x + y w of norm p; the two primes above p are it and its conjugate
            found = None
            for y in range(1, isqrt(4 * p // 3) + 2):
                d = 4 * p - 3 * y * y
                if d < 0:
                    break
                s = isqrt(d)
                if s * s == d and (y + s) % 2 == 0:
                    found = ((y + s) // 2, y)
                    break
            assert found and norm(found) == p
            out.append(found)
            out.append(conj(found))
            assert not divides(found, conj(found))
    return out
