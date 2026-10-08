"""Floating-point Eisenstein-integer toolkit for check_full_theta.py.
Elements a+b*omega are pairs (a,b); omega^2=-1-omega.
"""
import math, cmath
import numpy as np

OM = complex(-0.5, math.sqrt(3) / 2)
LAM = 1 + 2 * OM  # i*sqrt(3)


def mul(x, y):
    a, b = x
    c, d = y
    return (a * c - b * d, a * d + b * c - b * d)


def conj(x):
    a, b = x
    return (a - b, -b)


def norm(x):
    a, b = x
    return a * a - a * b + b * b


def val(x):
    return x[0] + x[1] * OM


def divides(p, x):
    """return x/p if p | x else None"""
    t = mul(x, conj(p))
    q = norm(p)
    if t[0] % q or t[1] % q:
        return None
    return (t[0] // q, t[1] // q)


def is_rat_prime(n):
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    r = int(math.isqrt(n))
    for d in range(3, r + 1, 2):
        if n % d == 0:
            return False
    return True


def primary_elements(bound):
    lim = int(2 * math.sqrt(bound)) + 3
    out = []
    for a in range(-lim, lim + 1):
        if a % 3 != 1:
            continue
        for b in range(-lim, lim + 1):
            if b % 3 != 0:
                continue
            n = a * a - a * b + b * b
            if 0 < n <= bound:
                out.append((a, b))
    out.sort(key=lambda t: (norm(t), t))
    return out


def powmod_eis(x, e, p):
    """x^e in Z[omega]/(p), p rational prime"""
    z = (1, 0)
    x = (x[0] % p, x[1] % p)
    while e:
        if e & 1:
            z = mul(z, x)
            z = (z[0] % p, z[1] % p)
        x = mul(x, x)
        x = (x[0] % p, x[1] % p)
        e >>= 1
    return z


def primitive_root(q):
    n = q - 1
    fs = []
    m = n
    d = 2
    while d * d <= m:
        if m % d == 0:
            fs.append(d)
            while m % d == 0:
                m //= d
        d += 1
    if m > 1:
        fs.append(m)
    g = 2
    while True:
        if all(pow(g, n // f, q) != 1 for f in fs):
            return g
        g += 1


class Prime:
    """primary prime pi (pi = 1 mod 3), not dividing 3"""

    def __init__(self, pi):
        self.pi = pi
        self.q = norm(pi)
        a, b = pi
        if b % self.q != 0 and is_rat_prime(self.q):
            self.deg = 1
            self.r = (-a * pow(b, -1, self.q)) % self.q  # image of omega
            assert (self.r * self.r + self.r + 1) % self.q == 0
        else:
            assert b == 0
            self.deg = 2
            self.p = abs(a)
            assert self.q == self.p * self.p
        self._g3 = None

    def red(self, x):
        if self.deg == 1:
            return (x[0] + x[1] * self.r) % self.q
        return (x[0] % self.p, x[1] % self.p)

    def sextic_index(self, x):
        """return k in 0..5 with (x/pi)_6 = zeta6^k, zeta6=-omega^2=exp(2 pi i/6); None if pi|x.
        Requires q = 1 mod 6 (pi not above 2)."""
        q = self.q
        assert q % 6 == 1
        if self.deg == 1:
            xx = self.red(x)
            if xx == 0:
                return None
            t = pow(xx, (q - 1) // 6, q)
            z6 = (-self.r * self.r) % q
            w = 1
            for k in range(6):
                if w == t:
                    return k
                w = w * z6 % q
            raise ValueError
        xx = self.red(x)
        if xx == (0, 0):
            return None
        t = powmod_eis(xx, (q - 1) // 6, self.p)
        z6 = (1 % self.p, 1 % self.p)  # -omega^2 = 1+omega
        w = (1, 0)
        for k in range(6):
            if (w[0] % self.p, w[1] % self.p) == t:
                return k
            w = mul(w, z6)
            w = (w[0] % self.p, w[1] % self.p)
        raise ValueError

    def cubic_index(self, x):
        """k in 0..2 with (x/pi)_3 = omega^k; None if pi | x"""
        q = self.q
        if self.deg == 1:
            xx = self.red(x)
            if xx == 0:
                return None
            t = pow(xx, (q - 1) // 3, q)
            if t == 1:
                return 0
            if t == self.r:
                return 1
            assert t == self.r * self.r % q
            return 2
        xx = self.red(x)
        if xx == (0, 0):
            return None
        t = powmod_eis(xx, (q - 1) // 3, self.p)
        if t == (1, 0):
            return 0
        if t == (0, 1):
            return 1
        assert t == ((-1) % self.p, (-1) % self.p), t
        return 2

    def gtilde(self):
        """normalized cubic Gauss sum  q^{-1/2} sum_x (x/pi)_3 breve_e(x/pi),
        breve_e(z)=exp(2 pi i (z + zbar))."""
        if self._g3 is not None:
            return self._g3
        q = self.q
        a, b = self.pi
        if self.deg == 1:
            # powers of a primitive root by doubling: pw[k]=gen^k mod q
            gen = primitive_root(q)
            pw = np.array([1], dtype=np.int64)
            cur = gen % q  # gen^{len(pw)}
            while len(pw) < q - 1:
                pw = np.concatenate([pw, pw * cur % q])
                cur = cur * cur % q
            pw = pw[: q - 1]
            t = pow(gen, (q - 1) // 3, q)
            jj = 1 if t == self.r else 2
            assert t == pow(self.r, jj, q)
            k = (np.arange(q - 1, dtype=np.int64) * jj) % 3
            ch = np.array([1 + 0j, OM, OM * OM])[k]
            ph = np.exp(2j * np.pi * ((pw * ((2 * a - b) % q)) % q) / q)
            g = np.sum(ch * ph) / math.sqrt(q)
        else:
            p = self.p
            g = 0j
            for u in range(p):
                for v in range(p):
                    k = self.cubic_index((u, v))
                    if k is None:
                        continue
                    # x/pi with pi=(a,0): 2Re((u+v omega)/a) = (2u - v)/a
                    g += OM ** k * cmath.exp(2j * math.pi * (2 * u - v) / a)
            g /= p
        self._g3 = complex(g)
        return self._g3


def build(bound):
    """return (elements, factorization dict, list of Prime objects)"""
    els = primary_elements(bound)
    primes = {}
    fact = {}
    plist = []
    for n in els:
        if n == (1, 0):
            fact[n] = []
            continue
        r = n
        fs = []
        for P in plist:
            if P.q > norm(r):
                break
            while True:
                rr = divides(P.pi, r)
                if rr is None:
                    break
                fs.append(P)
                r = rr
            if r == (1, 0):
                break
        if r != (1, 0):
            # r must be a new primary prime (possibly times nothing)
            assert r == n, (n, r)
            P = Prime(n)
            plist.append(P)
            fs.append(P)
        fact[n] = fs
    return els, fact, plist
