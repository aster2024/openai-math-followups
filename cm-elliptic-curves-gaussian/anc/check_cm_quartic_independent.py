from pathlib import Path as _Path
_RESULTS = _Path(__file__).resolve().parent / 'results'
_RESULTS.mkdir(exist_ok=True)
def _quiet(*args, **kwargs):
    pass

"""Independent exact checks of the CM twists, conductors and local factors.

No L-function zero computation.  Gaussian integer arithmetic and finite
residue-field arithmetic use Python integers only; SymPy factors integer
norms.  Conductor table uses the proved local fourth-power bound U_7.
"""
from pathlib import Path
from collections import Counter
import json, math, time
import sympy

START = time.time()
ONE=(1,0)
def mul(z,w): return (z[0]*w[0]-z[1]*w[1],z[0]*w[1]+z[1]*w[0])
def norm(z): return z[0]**2+z[1]**2
def conj(z): return (z[0],-z[1])
def powg(z,n):
    out=ONE
    while n:
        if n&1: out=mul(out,z)
        z=mul(z,z);n//=2
    return out
def divexact(z,w):
    top=mul(z,conj(w)); den=norm(w)
    if top[0]%den or top[1]%den: return None
    return (top[0]//den,top[1]//den)
def roundrat(a,n): return (2*a+n)//(2*n)
def rem(z,w):
    top=mul(z,conj(w)); den=norm(w)
    quotient=(roundrat(top[0],den),roundrat(top[1],den))
    prod=mul(quotient,w)
    return (z[0]-prod[0],z[1]-prod[1])
LAMBDA=(1,1)
UNITS=[ONE,(0,1),(-1,0),(0,-1)]
def primary(z):
    for j,u in enumerate(UNITS):
        w=mul(u,z)
        if rem((w[0]-1,w[1]),powg(LAMBDA,3))==(0,0):
            return w,j
    raise AssertionError(('not odd',z))
def splitprime(p):
    for a in range(1,math.isqrt(p)+1):
        b=math.isqrt(p-a*a)
        if a*a+b*b==p: return (a,b)
    raise AssertionError(p)
def quartic_at_prime(d,z):
    p=norm(z)
    ires=(-z[0]*pow(z[1],-1,p))%p
    lookup={pow(ires,j,p):j for j in range(4)}
    return lookup[pow(d%p,(p-1)//4,p)]
def jacobi(d,z):
    exponent=0
    left=z
    for p in sympy.factorint(norm(z)):
        p=int(p)
        assert p!=2 and d%p!=0,(d,z,p)
        if p%4==3:
            while True:
                quotient=divexact(left,(p,0))
                if quotient is None: break
                left=quotient
            continue  # rational d has quartic symbol 1 in F_(p^2)
        pi=splitprime(p)
        for q in (pi,conj(pi)):
            value=quartic_at_prime(d,q)
            while True:
                quotient=divexact(left,q)
                if quotient is None: break
                left=quotient;exponent+=value
    assert norm(left)==1,(d,z,left)
    return exponent%4
def psi(d,z):
    # d need not be positive.  Ideal (z) is prime to 2d.
    pr,j=primary(z)
    twist=jacobi(d,pr)
    return mul(UNITS[(-twist)%4],pr)
def legendre(x,p):
    x%=p
    if not x:return 0
    return 1 if pow(x,(p-1)//2,p)==1 else -1
def trace_curve(d,p):
    return -sum(legendre(x*x*x-d*x,p) for x in range(p))

# Independent good Euler comparisons, including the inert rational prime 3.
comparisons=[]
ds=[-15,-12,-9,-8,-7,-5,-4,-3,-2,-1,1,2,3,4,5,7,8,9,12,15,
    sympy.Rational(1,2),sympy.Rational(-3,5)]
for rational_d in ds:
    a,b=map(int,sympy.fraction(rational_d))
    dint=a*b**3  # x=(1/b)^2 X, y=(1/b)^3 Y
    for p in sympy.primerange(3,180):
        p=int(p)
        if dint%p==0:continue
        ap=trace_curve((a*pow(b,-1,p))%p,p)
        if p%4==1:
            pi=splitprime(p)
            first=psi(dint,pi);second=psi(dint,conj(pi))
            assert first[1]+second[1]==0,(rational_d,p,first,second)
            predicted=first[0]+second[0]
            assert mul(first,second)==(p,0)
        else:
            assert psi(dint,(p,0))==(-p,0),(rational_d,p)
            predicted=0
        assert ap==predicted,(rational_d,p,ap,predicted)
        comparisons.append({'D':str(rational_d),'p':p,'trace':ap})

# Compute the exact finite character at lambda, not a guessed product of
# seed and twist conductors.  U_7 consists of fourth powers: successive
# squaring maps U_m onto U_(m+2) for m>=3 in Q_2(i).
modulus=powg(LAMBDA,7)
residues={rem((a,b),modulus) for a in range(16) for b in range(16)}
units=sorted(z for z in residues if (z[0]+z[1])%2)
assert len(residues)==128 and len(units)==64
generators=[(0,1),(-1,2),(5,0)]
generated={rem(mul(mul(powg(generators[0],a),powg(generators[1],b)),
                   powg(generators[2],c)),modulus)
           for a in range(4) for b in range(4) for c in range(4)}
assert generated==set(units)
tables=[]
for d in [a*2**e for e in (0,1) for a in range(1,16,2)]:
    odd=d//(2 if d%2==0 else 1)
    # CRT alpha=1 (mod odd), alpha=z (mod lambda^7).
    inv=pow(odd,-1,128)
    values={}
    for z in units:
        step=rem(((z[0]-1)*inv,z[1]*inv),modulus)
        alpha=(1+odd*step[0],odd*step[1])
        assert rem((alpha[0]-z[0],alpha[1]-z[1]),modulus)==(0,0)
        pr,j=primary(alpha)
        exponent=(j-jacobi(d,pr))%4
        values[z]=exponent
    for z in units:
        for w in units:
            assert values[rem(mul(z,w),modulus)]==(values[z]+values[w])%4
    candidates=[]
    for m in range(8):
        mm=powg(LAMBDA,m)
        if all(value==0 for z,value in values.items()
               if rem((z[0]-1,z[1]),mm)==(0,0)):
            candidates.append(m)
    exponent=min(candidates)
    assert exponent>=1
    witnesses=[{'class':list(z),'value_i_exponent':value}
               for z,value in values.items() if value and
               rem((z[0]-1,z[1]),powg(LAMBDA,exponent-1))==(0,0)]
    assert witnesses
    tables.append({'rational_local_class':d,'lambda_conductor_exponent':exponent,
                   'rational_2_conductor_exponent':exponent+2,
                   'unit_classes_tested':len(values),
                   'nontriviality_witness':witnesses[0],
                   'generator_values_i_exponents':
                       [values[rem(g,modulus)] for g in generators]})

report={'status':'PASS','elapsed_seconds':time.time()-START,
        'good_euler_comparisons':len(comparisons),'comparisons':comparisons,
        'dyadic_conductor_table':tables,
        'scope':'Exact finite checks. The global CM identification and the local upper bound are proved in the paper.'}
(_RESULTS / 'cm_quartic_independent.json').write_text(json.dumps(report,indent=2)+'\n')
_quiet(json.dumps({k:v for k,v in report.items() if k!='comparisons'},indent=2))

print('check_cm_quartic_independent.py: PASS (see results/; scope in README.md)')
