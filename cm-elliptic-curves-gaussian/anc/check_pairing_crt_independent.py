from pathlib import Path as _Path
_RESULTS = _Path(__file__).resolve().parent / 'results'
_RESULTS.mkdir(exist_ok=True)
def _quiet(*args, **kwargs):
    pass

"""Exact two-prime CRT test of BOTH Gauss conversions.

This is a finite algebra model, not a construction of global theta over F.
The two selected sextic characters obey symmetric reciprocity.  All sums
are computed in Q[z]/Phi_(6*13*37), including their positive square roots
via quadratic Gauss sums. Arbitrary unitary background characters remain
external formal factors; they never enter a finite Fourier expansion.
"""
from pathlib import Path
import json, time
from itertools import product
from functools import lru_cache
import sympy as s

start=time.time()
P,Q=13,37
M=6*P*Q
x=s.symbols('x')
from fractions import Fraction as _Fraction
from math import gcd as _gcd, lcm as _lcm

class _RationalPolynomial:
    """Exact Q[x], stored as a SymPy ZZ numerator and one positive denominator."""
    __slots__ = ('numerator', 'denominator')

    @classmethod
    def _new(cls, numerator, denominator=1):
        if denominator < 0:
            numerator, denominator = -numerator, -denominator
        common = _gcd(int(denominator), int(numerator.content()))
        if common != 1:
            numerator = numerator.quo_ground(common)
            denominator //= common
        result = object.__new__(cls)
        result.numerator = numerator
        result.denominator = int(denominator)
        return result

    def __hash__(self):
        return hash((self.numerator, self.denominator))

    def __eq__(self, other):
        if isinstance(other, int):
            other = fmpq_poly([other])
        if not isinstance(other, _RationalPolynomial):
            return False
        return (self.denominator == other.denominator
                and self.numerator == other.numerator)

    def __neg__(self):
        return self._new(-self.numerator, self.denominator)

    def __add__(self, other):
        if isinstance(other, int):
            other = fmpq_poly([other])
        denominator = _lcm(self.denominator, other.denominator)
        numerator = (self.numerator.mul_ground(denominator // self.denominator)
                     + other.numerator.mul_ground(denominator // other.denominator))
        return self._new(numerator, denominator)

    __radd__ = __add__

    def __sub__(self, other):
        return self + (-other)

    def __mul__(self, other):
        if isinstance(other, _RationalPolynomial):
            return self._new(self.numerator * other.numerator,
                             self.denominator * other.denominator)
        return self.mul_ground(other)

    __rmul__ = __mul__

    def mul_ground(self, scalar):
        if hasattr(scalar, 'p') and hasattr(scalar, 'q'):
            scalar = _Fraction(int(scalar.p), int(scalar.q))
        else:
            scalar = _Fraction(scalar)
        return self._new(self.numerator.mul_ground(scalar.numerator),
                         self.denominator * scalar.denominator)

    def __mod__(self, modulus):
        assert modulus.denominator == 1 and modulus.numerator.LC() == 1
        return self._new(self.numerator.rem(modulus.numerator, auto=False), self.denominator)

    def all_coeffs(self):
        return [_Fraction(int(c), self.denominator)
                for c in self.numerator.all_coeffs()]

    def degree(self):
        return self.numerator.degree()

def fmpq_poly(coefficients):
    fractions = [_Fraction(c) for c in coefficients]
    denominator = 1
    for c in fractions:
        denominator = _lcm(denominator, c.denominator)
    integers = [c.numerator * (denominator // c.denominator) for c in fractions]
    numerator = s.Poly.from_list(list(reversed(integers)) or [0], x, domain=s.ZZ)
    return _RationalPolynomial._new(numerator, denominator)

mod=fmpq_poly(list(reversed([int(c) for c in s.Poly(s.cyclotomic_poly(M,x),x).all_coeffs()])))
ZERO=fmpq_poly([]);ONE=fmpq_poly([1])
def reduce(poly):return poly%mod
@lru_cache(maxsize=4096)
def phase(j):
    cs=[0]*(j%M+1);cs[-1]=1
    return reduce(fmpq_poly(cs))
@lru_cache(maxsize=8192)
def mul(a,b):return reduce(a*b)
def power(a,n):
    out=ONE
    while n:
        if n&1:out=mul(out,a)
        a=mul(a,a);n//=2
    return out
@lru_cache(maxsize=256)
def conj(a):
    cs=[0]*M
    for j,c in enumerate(reversed(a.all_coeffs())):cs[(-j)%M]+=c
    return reduce(fmpq_poly(cs))
def summed(exponents):
    cs=[0]*M
    for j in exponents:cs[j%M]+=1
    return reduce(fmpq_poly(cs))

logs={}
for p,orientation in ((P,1),(Q,-1)):
    g=int(s.primitive_root(p));d={};v=1
    for j in range(p-1):d[v]=(orientation*j)%6;v=v*g%p
    logs[p]=d
assert logs[P][Q%P]==logs[Q][P%Q]
N=[1,P,Q,P*Q]
def prime_factors(n):return [p for p in (P,Q) if n%p==0]
def chi_exp(n,r):
    if any(r%p==0 for p in prime_factors(n)):return None
    return sum(logs[p][r%p] for p in prime_factors(n))%6
def chi(n,r,j=1):
    e=chi_exp(n,r)
    return ZERO if e is None else phase((M//6)*e*j)
roots={1:ONE}
for p in (P,Q):
    roots[p]=summed((M//6)*3*logs[p][r]+(M//p)*r for r in range(1,p))
    assert mul(roots[p],roots[p])==ONE*p
roots[P*Q]=mul(roots[P],roots[Q])
def gamma(n,j):
    total=summed((M//6)*j*chi_exp(n,r)+(M//n)*r
                 for r in range(n) if chi_exp(n,r) is not None)
    return mul(total,roots[n]).mul_ground(s.Rational(1,n))
@lru_cache(maxsize=32)
def pair_gauss(a,b,first=True):
    n=a*b
    def e(r):
        ca,cb=chi_exp(a,r),chi_exp(b,r)
        if ca is None or cb is None:return None
        return ca-cb if first else cb-ca
    total=summed((M//6)*e(r)+(M//n)*r
                 for r in range(n) if e(r) is not None)
    return mul(total,roots[n]).mul_ground(s.Rational(1,n))
def mobius(n):return (-1)**len(prime_factors(n))

gammas={(n,j):gamma(n,j) for n in N for j in (1,2,3,4,5)}
lam={1:ONE};G={1:ONE}
for p in (P,Q):
    lam[p]=-power(gammas[p,2],3)
    G[p]=mul(conj(chi(p,4)),gammas[p,3])
lam[P*Q]=mul(lam[P],lam[Q]);G[P*Q]=mul(G[P],G[Q])
a={n:mul(conj(lam[n]),gammas[n,2]) for n in N}

tests=[]
for n in N:
    assert mul(gammas[n,1],gammas[n,5])==ONE
    assert power(gammas[n,2],3)==lam[n]*mobius(n)
    assert mul(gammas[n,1],gammas[n,2])==mul(lam[n],G[n])*mobius(n)
    # Actual angular Mobius initialization: background bar(eta) is a
    # common formal factor on both sides of this exact equality.
    assert gammas[n,5]*mobius(n)==mul(a[n],conj(G[n]))
for aa,bb in product(N,repeat=2):
    if s.gcd(aa,bb)!=1:continue
    first=mul(mul(a[aa],conj(a[bb])),pair_gauss(aa,bb,True))
    first_expected=mul(G[aa],conj(G[bb]))*(mobius(aa)*mobius(bb))
    assert first==first_expected,(aa,bb,'first')
    second=mul(first_expected,pair_gauss(aa,bb,False))
    second_expected=mul(a[aa],conj(a[bb]))
    assert second==second_expected,(aa,bb,'second')
    twist=mul(a[aa],a[bb]);twist=mul(twist,chi(bb,aa,4))
    assert a[aa*bb]==twist,(aa,bb,'twisted multiplicativity')
    tests.append([aa,bb])

# Check finite residue Poisson with every shared-prime exclusion divisor.
# Use delta weights at all residues; Fourier inversion is then exact in
# the same cyclotomic field. This also includes primitive modulus one.
@lru_cache(maxsize=128)
def local_dual(p,sgn,k):
    return summed(-(M//6)*sgn*logs[p][h]-(M//p)*h*k
                  for h in range(1,p))
@lru_cache(maxsize=4096)
def inverse_gauss(aa,bb,k):
    modulus=aa*bb
    dual=ONE
    # Exact CRT factorization of the additive Fourier phase.  The global
    # Gauss sums above were independently computed by direct summation.
    for p in prime_factors(modulus):
        sgn=1 if aa%p==0 else -1
        local_k=(k*pow(modulus//p,-1,p))%p
        dual=mul(dual,local_dual(p,sgn,local_k))
    return mul(mul(pair_gauss(aa,bb,True),roots[modulus]),dual).mul_ground(s.Rational(1,modulus))
poisson=0
for aa,bb in product(N,repeat=2):
    if s.gcd(aa,bb)!=1:continue
    modulus=aa*bb
    for C in s.divisors((P*Q)//modulus):
        C=int(C)
        for row in range(P*Q):
            direct=mul(chi(aa,row),conj(chi(bb,row)))
            if s.gcd(row,C)!=1:direct=ZERO
            transformed=ZERO
            for d in s.divisors(C):
                d=int(d)
                if row%d:continue
                rho_d=mul(chi(aa,d),conj(chi(bb,d)))
                transformed+=mul(rho_d,inverse_gauss(aa,bb,(row//d)%modulus))*mobius(d)
            assert reduce(transformed)==direct,(aa,bb,C,row)
            poisson+=1
    _quiet('PASS finite Poisson pair',aa,bb,'total cases',poisson,flush=True)

r={'status':'PASS','elapsed_seconds':time.time()-start,
   'cyclotomic_order':M,'exact_field_degree':mod.degree(),
   'coprime_pairs':tests,'finite_residue_Poisson_cases':poisson,
   'scope':'Exact finite CRT model and all conjugations/zero extensions, not an analytic mean-square or theta certificate.'}
(_RESULTS / 'pairing_crt_independent.json').write_text(json.dumps(r,indent=2)+'\n')
_quiet(json.dumps(r,indent=2))

print('check_pairing_crt_independent.py: PASS (see results/; scope in README.md)')
