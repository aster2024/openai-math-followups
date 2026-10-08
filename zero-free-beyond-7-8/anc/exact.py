"""Small exact arithmetic library; Python standard library only."""
from fractions import Fraction as Q


class Interval:
    def __init__(self, lo, hi=None):
        self.lo = Q(lo)
        self.hi = self.lo if hi is None else Q(hi)
        assert self.lo <= self.hi

    @staticmethod
    def cast(x):
        return x if isinstance(x, Interval) else Interval(x)

    def __add__(self, other):
        b = self.cast(other)
        return Interval(self.lo + b.lo, self.hi + b.hi)

    __radd__ = __add__

    def __neg__(self):
        return Interval(-self.hi, -self.lo)

    def __sub__(self, b):
        return self + -self.cast(b)

    def __rsub__(self, b):
        return self.cast(b) + -self

    def __mul__(self, other):
        b = self.cast(other)
        vals = [a * c for a in (self.lo, self.hi) for c in (b.lo, b.hi)]
        return Interval(min(vals), max(vals))

    __rmul__ = __mul__

    def inverse(self):
        assert not self.lo <= 0 <= self.hi, "interval contains zero"
        return Interval(1 / self.hi, 1 / self.lo)

    def __truediv__(self, b):
        return self * self.cast(b).inverse()

    def __rtruediv__(self, b):
        return self.cast(b) * self.inverse()

    def __pow__(self, n):
        assert n >= 0
        z = Interval(1)
        for _ in range(n):
            z = z * self
        return z

    def __repr__(self):
        return f"[{self.lo}, {self.hi}]"


class Field:
    """Q[t]/(monic polynomial), coefficients in ascending order."""
    def __init__(self, modulus):
        self.mod = tuple(map(Q, modulus))
        assert self.mod[-1] == 1
        self.degree = len(self.mod) - 1

    def __call__(self, coeffs):
        if isinstance(coeffs, Element):
            assert coeffs.field is self
            return coeffs
        if not isinstance(coeffs, (list, tuple)):
            coeffs = [coeffs]
        return Element(self, coeffs)


class Element:
    def __init__(self, field, coeffs):
        self.field = field
        a = list(map(Q, coeffs))
        while len(a) > field.degree:
            v = a.pop()
            k = len(a) - field.degree
            for j in range(field.degree):
                a[k + j] -= v * field.mod[j]
        a.extend([Q(0)] * (field.degree - len(a)))
        self.a = tuple(a)

    def __add__(self, other):
        if isinstance(other, Poly):
            return other + self
        b = self.field(other)
        return self.field([x + y for x, y in zip(self.a, b.a)])

    __radd__ = __add__

    def __neg__(self):
        return self.field([-a for a in self.a])

    def __sub__(self, b):
        if isinstance(b, Poly):
            return Poly.cast(self) - b
        return self + -self.field(b)

    def __rsub__(self, b):
        if isinstance(b, Poly):
            return b - self
        return self.field(b) + -self

    def __mul__(self, other):
        if isinstance(other, Poly):
            return other * self
        b = self.field(other)
        out = [Q(0)] * (2 * self.field.degree - 1)
        for i, x in enumerate(self.a):
            for j, y in enumerate(b.a):
                out[i + j] += x * y
        return self.field(out)

    __rmul__ = __mul__

    def inverse(self):
        d = self.field.degree
        cols = [(self * self.field([0] * j + [1])).a for j in range(d)]
        m = [[cols[j][i] for j in range(d)] + [Q(i == 0)] for i in range(d)]
        for j in range(d):
            k = next(k for k in range(j, d) if m[k][j])
            m[k], m[j] = m[j], m[k]
            v = m[j][j]
            m[j] = [x / v for x in m[j]]
            for i in range(d):
                if i != j:
                    v = m[i][j]
                    m[i] = [x - v * y for x, y in zip(m[i], m[j])]
        z = self.field([m[i][-1] for i in range(d)])
        assert self * z == 1
        return z

    def __truediv__(self, b):
        return self * self.field(b).inverse()

    def __rtruediv__(self, b):
        return self.field(b) * self.inverse()

    def __pow__(self, n):
        if n < 0:
            return self.inverse() ** (-n)
        z = self.field(1)
        for _ in range(n):
            z *= self
        return z

    def __eq__(self, other):
        if isinstance(other, Poly):
            return other == self
        return self.a == self.field(other).a

    def __bool__(self):
        return any(self.a)

    def interval(self, root_interval):
        z = Interval(0)
        for a in reversed(self.a):
            z = z * root_interval + a
        return z

    def __repr__(self):
        return "(" + ", ".join(map(str, self.a)) + ")"


class Poly:
    """Bivariate exact polynomials in delta and y."""
    def __init__(self, terms=None):
        assert all(not isinstance(v, float) for v in (terms or {}).values())
        self.terms = {k: (v if isinstance(v, Element) else Q(v))
                      for k, v in (terms or {}).items() if v != 0}

    @staticmethod
    def cast(x):
        return x if isinstance(x, Poly) else Poly({(0, 0): x})

    def __add__(self, other):
        b = self.cast(other)
        a = self.terms.copy()
        for k, v in b.terms.items():
            a[k] = a.get(k, 0) + v
        return Poly(a)

    __radd__ = __add__

    def __neg__(self):
        return Poly({k: -v for k, v in self.terms.items()})

    def __sub__(self, b):
        return self + -self.cast(b)

    def __rsub__(self, b):
        return self.cast(b) + -self

    def __mul__(self, other):
        b = self.cast(other)
        a = {}
        for (i, j), v in self.terms.items():
            for (k, l), w in b.terms.items():
                key = (i + k, j + l)
                a[key] = a.get(key, 0) + v * w
        return Poly(a)

    __rmul__ = __mul__

    def __truediv__(self, b):
        assert not isinstance(b, Poly)
        b = b if isinstance(b, Element) else Q(b)
        return Poly({k: v / b for k, v in self.terms.items()})

    def __pow__(self, n):
        z = Poly.cast(1)
        for _ in range(n):
            z *= self
        return z

    def __eq__(self, other):
        return self.terms == self.cast(other).terms

    def evaluate(self, d, y):
        return sum(v * d ** i * y ** j for (i, j), v in self.terms.items())


DELTA = Poly({(1, 0): Q(1)})
Y = Poly({(0, 1): Q(1)})


def endpoint_numerator(ell, b, c=Q(4, 9), alpha=Q(5, 6), long_beta=None):
    """Expand -108 J E from the complete endpoint expression."""
    if long_beta is None:
        long_beta = alpha
    d, y = DELTA, Y
    x = Q(1, 2) - y
    a = 2 - 2 * c * x
    bb = 1 - x
    dd = a + bb
    pp = a * bb
    jj = (alpha - d) * dd + d * pp
    h = (1 + b + 3 * ell) / 2
    e0 = -Q(1, 4) + b / 6 + 5 * ell / 4 - d * (b / 2 + ell * y)
    return -108 * jj * e0 - 54 * h * (long_beta - d) * d * pp


def general_coefficients(ell, b, c):
    a0 = 27*b*c/2 - 54*b - 81*c*ell/2 - 27*c/2 + 81*ell + 27
    a1 = -108*b*c + 108*b + 54*c*ell + 54
    b1 = 126*b*c - 18*b + 180*c*ell - 54*c - 45*ell - 18
    c1 = -30*b*c - 15*b - 225*c*ell + 45*c - 225*ell/2 + Q(45,2)
    a2 = 162*b*c - 54*c*ell + 54*c + 108*ell
    b2 = -81*b*c - 225*c*ell + 9*c + 90*ell
    a3 = 216*c*ell
    return a0, a1, b1, c1, a2, b2, a3


def check(label, condition):
    assert condition, label
    print("PASS", label)
