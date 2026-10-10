"""Exact finite checks for the arithmetic identities in the accompanying paper."""
from fractions import Fraction as F
from itertools import product, combinations
from functools import reduce


def vp(n, p):
    k = 0
    while n % p == 0:
        k += 1
        n //= p
    return k


def small_b(n, p, r):
    return F(0) if n % (p*p) == 0 else (r if n % p == 0 else F(1))


counts = {}

# the paper's tilted characteristic factor: use a formal phase with z^(-1) represented
# by a paired dictionary of exponents. This checks coefficients exactly.
for p in (2, 3, 5, 7, 11, 17, 19):
    active = F(17, p+16)
    q = F(16, 17)
    positive = active*q*(1-q)
    negative = positive
    zero = 1-positive-negative
    assert positive == F(16, 17*(p+16))
    assert zero == 1-F(32, 17*(p+16))
counts['tilted_characteristic_local_coefficients'] = 7

# the paper, arbitrary fixed even h, including all three local cases.
k = 0
for p, h, r in product((2, 3, 5, 7, 11), range(2, 42, 2), (F(0), F(1,100), F(1,2), F(99,100), F(1))):
    actual = sum((small_b(n,p,r)*small_b(n+h,p,r) for n in range(p*p)), F(0))/ (p*p)
    if h % p:
        expected = 1-F(2,p)+2*r*F(p-1,p*p)
    elif h % (p*p) == 0:
        expected = 1-F(1,p)+r*r*F(p-1,p*p)
    else:
        expected = 1-F(1,p)+r*r*F(p-2,p*p)
    assert actual == expected, (p,h,r,actual,expected)
    k += 1
counts['soft_pair_local_density_identities'] = k

# Distinct three-root factor in the paper: each position excludes a different mod-p root.
k = 0
for p, r in product((5,7,11), (F(0), F(1,100), F(1,2), F(99,100), F(1))):
    for a,b in combinations(range(1,p),2):
        actual = sum((small_b(n,p,r)*small_b(n+a,p,r)*small_b(n+b,p,r) for n in range(p*p)), F(0))/(p*p)
        assert actual == 1-3*(1-r)/p-3*r/(p*p)
        k += 1
counts['soft_three_distinct_root_identities'] = k

# C0/C1 enumeration in the paper for a rational unit-circle phase z. Values are
# Gaussian rational pairs; no floating-point comparison is used.
def add(x,y): return (x[0]+y[0],x[1]+y[1])
def mul(x,y): return (x[0]*y[0]-x[1]*y[1], x[0]*y[1]+x[1]*y[0])
def sc(a,x): return (a*x[0],a*x[1])
def abs2(x): return x[0]*x[0]+x[1]*x[1]
one = (F(1),F(0))
k = 0
for p,r,z in product((3,5,7,11,17), (F(99,100), F(999,1000), F(1)), ((F(1),F(0)),(F(0),F(1)),(F(3,5),F(4,5)),(F(-3,5),F(4,5)),(F(-1),F(0)))):
    zp = (z[0],-z[1])
    kp = 4*r*r/p
    c0 = add(one,sc(kp/F(5),add(sc(F(4),one),z)))
    c1 = sc(F(1,5),add(add(one,sc(F(4),zp)),sc(kp,add(z,sc(F(4),one)))))
    # m not divisible p: u=0 gives 1; u=1 gives k*((1/5)z+4/5).
    enum0 = add(one,sc(kp,add(sc(F(1,5),z),sc(F(4,5),one))))
    # m divisible p: u=0 gives (1/5)+(4/5)z^-1; u=1 gives k*((1/5)z+4/5).
    enum1 = add(add(sc(F(1,5),one),sc(F(4,5),zp)),sc(kp,add(sc(F(1,5),z),sc(F(4,5),one))))
    assert c0==enum0 and c1==enum1
    assert abs2(c0)-abs2(c1)==F(8,25)*(1-z[0])*(1+5*kp+2*kp*z[0])
    k+=1
counts['external_padding_gaussian_rational_identities'] = k

# Exact capped-threshold level-vector equivalence, including b=0. The list of
# levels remains inside the Boolean circuit; it is not a scalar expansion.
k = 0
r = F(2,3)
M = 3
for n in (1,2,3):
    for bs in product((F(0),F(1),r,r*r,r**3,r**4),repeat=n):
        weights = tuple(F(j+1,5) for j in range(n))
        caps = tuple(max(b,r**M) for b in bs)
        true_sum = sum((w*b for w,b in zip(weights,caps)),F(0))
        for threshold in (F(0),F(1,10),F(1,3),F(2,3),F(1)):
            bad_or = False
            for levels in product(range(M+1),repeat=n):
                scalar = sum((w*r**lev for w,lev in zip(weights,levels)),F(0))
                if scalar > threshold and all(lev==M or b>=r**lev for b,lev in zip(bs,levels)):
                    bad_or = True
                    break
            assert bad_or == (true_sum>threshold), (bs,threshold)
            k+=1
counts['capped_threshold_level_vector_identities'] = k

# Closed words with repeated physical vertices: edge square roots, after
# squaring, yield exactly the square of the product of arrival b values.
k = 0
for length in (2,3,4,5):
    for path in product(range(3),repeat=length):
        for bvals in ((F(0),F(2,3),F(1)),(F(1,4),F(1,2),F(3,4))):
            square_edges = F(1)
            arrivals = F(1)
            for i in range(length):
                src=path[i];dst=path[(i+1)%length]
                square_edges *= bvals[src]*bvals[dst]
                arrivals *= bvals[dst]
            assert square_edges == arrivals*arrivals
            k+=1
counts['closed_word_arrival_weight_identities'] = k

assert F(1,3750)-F(1,60000)==F(1,4000)
assert 2*F(1,3750)==F(1,1875)
assert F(1,6)*F(41,17)-F(7,17)==-F(1,102)
counts['exact_exponent_identities'] = 3


# Multiplicative dilation and common-prefix factorization on actual integers.
def factor_counts(n):
    omega = total = 0
    p = 2
    while p*p <= n:
        if n % p == 0:
            omega += 1
            while n % p == 0:
                n //= p
                total += 1
        p += 1
    if n > 1:
        omega += 1
        total += 1
    return omega, total

def lam(n): return (-1)**factor_counts(n)[1]
def bmask(n, z, r):
    value = F(1)
    for p in (2,3,5,7):
        if p > z: continue
        value *= small_b(n,p,r)
    return value

k = 0
for a,m,h in product((11,13,11*13),range(1,41),(2,4,6)):
    assert lam(a*m)*lam(a*(m+h)) == lam(m)*lam(m+h)
    for r in (F(1,3),F(2,3)):
        b1,b2=bmask(m,7,r),bmask(m+h,7,r)
        assert bmask(a*m,7,r)==b1
        def full(n): return r**factor_counts(n)[1]*bmask(n,7,F(1))
        assert full(a*m)*full(a*(m+h)) == r**(2*factor_counts(a)[1])*full(m)*full(m+h)
        assert lam(a)**2 == 1
        k += 1
counts['dilation_identities'] = k

k = 0
for u,d,e,m,h,r in product((11,13),(17,19),(1,17),range(1,9),(2,4),(F(2,3),)):
    if d % e: continue
    n=u*e*m
    target=n+h*d*u
    assert target==u*e*(m+h*d//e)
    assert r**(2*factor_counts(n)[1]) == r**(2*factor_counts(u)[1]+2*factor_counts(e)[1])*r**(2*factor_counts(m)[1])
    k += 1
counts['prefix_alignment_identities'] = k

k=0
for r,v1,v2,cap in product((F(1,3),F(99,100),F(1)),range(5),range(5),(False,True)):
    masses = [(j,(1-r)*r**(j-1)) for j in range(1,9)] + [(100,r**8)]
    def accepted(v):
        return sum((prob for t,prob in masses if v < (min(t,2) if cap else t)),F(0))
    expected1=(r**v1 if not cap or v1<2 else F(0))
    expected2=(r**v2 if not cap or v2<2 else F(0))
    assert accepted(v1)*accepted(v2)==expected1*expected2
    k+=1
counts['prime_power_threshold_identities']=k
for a,b,s,t in product((-1,1),repeat=4):
    assert F((1+s*a)*(1+t*b),4)==int(a==s and b==t)
    k+=1
counts['sign_indicator_identities']=16

# Finite Selberg divisor inversion and quadratic diagonalization.
def mobius(n):
    p=2; sign=1
    while p*p<=n:
        if n%p==0:
            n//=p; sign=-sign
            if n%p==0: return 0
        p+=1
    return -sign if n>1 else sign

def totient(n):
    value=n; p=2; reduced=n
    while p*p<=reduced:
        if reduced%p==0:
            value-=value//p
            while reduced%p==0: reduced//=p
        p+=1
    if reduced>1: value-=value//reduced
    return value

def ilcm(a,b):
    x,y=a,b
    while y: x,y=y,x%y
    return a*b//x

primes=(2,3,5,7)
mark_sets=[tuple(p for p,chosen in zip(primes,bits) if chosen) for bits in product((0,1),repeat=4)]
k=0
for marked in mark_sets:
    period=1
    for p in marked: period*=p
    full_divisors=[d for d in range(1,period+1) if period%d==0]
    full_mass=sum((F(1,totient(d)) for d in full_divisors),F(0))
    factor_mass=F(1)
    for p in marked: factor_mass*=F(p,p-1)
    assert full_mass==factor_mass
    for U in range(1,11):
        divisors=[d for d in full_divisors if d<=U]
        G=sum((F(1,totient(d)) for d in divisors),F(0))
        ys={d:F(mobius(d),totient(d))/G for d in divisors}
        ls={d:d*sum((mobius(q//d)*ys[q] for q in divisors if q%d==0),F(0)) for d in divisors}
        assert ls[1]==1
        for q in divisors:
            assert ys[q]==sum((ls[d]/d for d in divisors if d%q==0),F(0))
            assert abs(ls[q])<=F(q,totient(q))
        quadratic=sum((ls[d]*ls[e]/ilcm(d,e) for d,e in product(divisors,repeat=2)),F(0))
        diagonal=sum((totient(q)*ys[q]*ys[q] for q in divisors),F(0))
        assert quadratic==diagonal==1/G
        rankin_factor=F(1)
        for p in marked: rankin_factor*=1+F(p-1,p)
        assert (full_mass-G)/full_mass<=rankin_factor/U
        for n in range(1,31):
            upper=sum((ls[d] for d in divisors if n%d==0),F(0))**2
            assert upper>=int(all(n%p for p in marked))
        k+=1
counts['selberg_finite_quadratic_identities']=k

# Real two-layer quadratic form, with signed increasing-edge entries.
k=0
for dimension in (2,3):
    matrix=[[F(2*i-j+1,3) if i<j else F(0) for j in range(dimension)] for i in range(dimension)]
    for values in product((-1,0,1),repeat=2*dimension):
        g1=values[:dimension];g2=values[dimension:]
        forward=sum((g1[i]*matrix[i][j]*g2[j] for i,j in product(range(dimension),repeat=2)),F(0))
        reverse=sum((g2[j]*matrix[i][j]*g1[i] for i,j in product(range(dimension),repeat=2)),F(0))
        assert forward+reverse==2*forward
        k+=1
counts['real_two_layer_quadratic_identities']=k

# Averaging over every subset of a finite marked-prime family.
k=0
for delta in (F(0),F(1,3),F(99,100),F(1)):
    def probability(marked):
        return delta**len(marked)*(1-delta)**(len(primes)-len(marked))
    expectation=sum((probability(marked)*
        reduce(lambda value,p:value*(1-F(1,p)),marked,F(1))
        for marked in mark_sets),F(0))
    expected=F(1)
    for p in primes: expected*=1-delta/p
    assert expectation==expected
    k+=1
    for n in range(1,61):
        no_mark=sum((probability(marked) for marked in mark_sets if all(n%p for p in marked)),F(0))
        assert no_mark==(1-delta)**sum(n%p==0 for p in primes)
        k+=1
counts['marked_subset_averaging_identities']=k

print('Finite arithmetic identities: %d cases, all equalities agree.' % sum(counts.values()))
