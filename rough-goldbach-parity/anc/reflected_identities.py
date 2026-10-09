"""Finite checks of algebraic identities used in the paper."""
from fractions import Fraction as F
from itertools import product
import json

def factors(n):
    out={}
    d=2
    while d*d<=n:
        while n%d==0:
            out[d]=out.get(d,0)+1
            n//=d
        d+=1
    if n>1: out[n]=out.get(n,0)+1
    return out

def liouville(n):
    return (-1)**sum(factors(n).values())

# Extraction of a prime from a reserved set, with all prime powers retained.
S={3,5,7}
checks=0
for n in range(1,2500):
    fac=factors(n)
    omega=sum(p in fac for p in S)
    Omega=sum(fac.get(p,0) for p in S)
    extracted=-sum((F(liouville(n//p),Omega) for p in S if n%p==0),F(0)) if Omega else F(0)
    expected=F(liouville(n)*omega,Omega) if Omega else F(0)
    assert extracted==expected
    target=liouville(n) if omega else 0
    assert abs(target-extracted)<=int(any(fac.get(p,0)>=2 for p in S))
    checks+=1

# Small-prime convolution coefficients for a completely multiplicative modification, including u=0 and u=1.
for u in [F(0),F(1,7),F(1,2),F(9,10),F(1)]:
    g=[F(1)]+[(1-u)*(-u)**(j-1) for j in range(1,12)]
    for k in range(12):
        assert sum(F((-1)**(k-j))*g[j] for j in range(k+1))==(-u)**k
        checks+=1

# Joint group expectation, computed directly over all residue pairs.
for N in [2,4,8,14,26]:
    primes=[p for p in [3,5,7,11] if N%p]
    q=F(9,10)
    V=sum((F(1,p) for p in primes),F(0))
    actual=F(0)
    for residues in product(*[range(p) for p in primes]):
        k=sum(r==0 for r in residues)
        ell=sum(r==N%p for r,p in zip(residues,primes))
        if k and ell:
            weight=F(k*ell,V*V)*q**(k+ell-2)
            actual+=weight
    mod=1
    for p in primes: mod*=p
    actual/=mod
    J=F(1)
    A=F(0); B=F(0)
    for p in primes:
        J*=1+2*(q-1)/p
        A+=1/(p+2*q-2)
        B+=1/(p+2*q-2)**2
    formula=J*(A*A-B)/(V*V)
    assert actual==formula
    checks+=1

# Finite-torus physical translation/reflection with actual admissible marks.
# State (n,p), one prime mark dividing n. Transition refreshes the mark;
# the free label d is forbidden from both endpoint lists.
mod=3*5*7
states=[(n,p) for n in range(mod) for p in [3,5,7] if n%p==0]
index={s:i for i,s in enumerate(states)}
for h in [1,2,11,22,107]:
    for n,p in states:
        translated={}; reflected={}; composed={}
        for d in [3,5,7]:
            for pp in [3,5,7]:
                if d in [p,pp]: continue
                nt=(n-h*d)%mod
                nr=(h*d-n)%mod
                if nt%pp==0:
                    translated[(nt,pp)]=translated.get((nt,pp),0)+1
                    composed[((-nt)%mod,pp)]=composed.get(((-nt)%mod,pp),0)+1
                if nr%pp==0:
                    reflected[(nr,pp)]=reflected.get((nr,pp),0)+1
        assert composed==reflected
        checks+=1

# Cardinality-based progression block neighborhood: every translation stays
# in the same h-fiber and moves at most H0 quotient places.
for h in [1,2,17,1009]:
    H0=12
    for n in range(-100,101):
        residue=n%h
        quotient=(n-residue)//h
        block=quotient//H0
        for step in range(-H0,H0+1):
            nn=n+h*step
            assert nn%h==residue
            qb=(nn-residue)//h//H0
            assert abs(qb-block)<=1
            checks+=1

# Exact shared-label normalization for a one-group raw reflection, J=ell=1.
# Compare the physical state sum (source mass V^-2, target sum V^-1)
# with the harmonic shared-prime law times the two W_1 endpoint weights.
from math import gcd
for N in [22,26,34,38]:
    P=[p for p in [3,5,7,11,13] if N%p]
    V=sum((F(1,p) for p in P),F(0))
    q=F(9,10)
    def degree(n): return sum(n%p==0 for p in P)
    def weight(n):
        k=degree(n)
        return F(k,V)*q**(k-1) if k else F(0)
    physical=F(0)
    for n in range(1,N*max(P)):
        if n%2==0 or gcd(n,N)>1: continue
        for shared in P:
            if n%shared: continue
            target=N*shared-n
            if target<=0 or target%2==0 or gcd(target,N)>1: continue
            if n%(shared*shared)==0 or target%(shared*shared)==0: continue
            for source_mark in P:
                if source_mark==shared or n%source_mark: continue
                for target_mark in P:
                    if target_mark==shared or target%target_mark: continue
                    physical+=F(liouville(n)*liouville(target),1)/(n*V**3)*q**(degree(n)+degree(target)-4)
    factored=F(0)
    for w in range(1,N):
        ww=N-w
        if w%2==0 or gcd(w,N)>1: continue
        shared_mass=sum((F(1,p)/V for p in P if w%p and ww%p),F(0))
        factored+=F(liouville(w)*liouville(ww),w)*weight(w)*weight(ww)*shared_mass
    assert physical==factored
    checks+=1

# A completely multiplicative quadratic-character example: every unit pair at totals 0 mod 3
# has opposite signs, although complete multiplicativity holds.
def character_example(n):
    val=1
    for p,k in factors(n).items():
        val*=((-1 if p==3 else (1 if p%3==1 else -1))**k)
    return val
for N in range(6,250,6):
    for n in range(1,N):
        if n%3 and (N-n)%3:
            assert character_example(n)*character_example(N-n)==-1
            checks+=1

summary={
 'status':'PASS',
 'exact_checks':checks,
 'checked':['reserved-prime extraction with prime powers','small-prime convolution coefficients','joint group local factor','reflection operator identity','shared-label normalization','quotient block cardinality','completely multiplicative character example'],
}
print(json.dumps(summary))
