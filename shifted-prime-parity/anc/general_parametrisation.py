#!/usr/bin/env python3
"""Exhaustive finite checks for general bilinear transport and local factors."""
from math import gcd
import json

def radical(n):
    n=abs(n);r=1;p=2
    while p*p<=n:
        if n%p==0:
            r*=p
            while n%p==0:n//=p
        p+=1
    return r*n

def mask(a,k,R,m,mp):
    d=a*abs(k);Q=d*R
    assert gcd(m,Q)==gcd(mp,Q)==1
    r=(mp*pow(m,-1,Q))%Q
    return (r-1)%d==0 and gcd((r-1)//d,R)==1

# Expected counterexample to replacing the full mask by oddness alone.
a_bad,b_bad,e_bad,n_bad,m_bad,mp_bad,v_bad,vp_bad=1,-6,3,9,1,5,5,17
assert m_bad*n_bad==a_bad*e_bad*v_bad+b_bad
assert mp_bad*n_bad==a_bad*e_bad*vp_bad+b_bad
assert e_bad%2==v_bad%2==vp_bad%2==1
assert (mp_bad-m_bad)%(a_bad*e_bad)!=0
assert gcd(e_bad,radical(2*a_bad*b_bad))!=1

bs=sorted(set(range(-18,19))|{25,-25,27,-27,36,-36,48,-48,49,-49})
bs.remove(0)
counts={"parameter_pairs":0,"forward":0,"forward_inverse":0,"mask_equivalence":0,"independent_inverse":0,"local_pairs":0}
by_pair={}
for a in range(1,7):
    for b in bs:
        if gcd(a,b)!=1:continue
        R=radical(2*a*b);key=f"{a},{b}"
        counts["parameter_pairs"]+=1
        c={"forward":0,"inverse":0,"mask":0,"admissible_odd_form":(a+b)%2==1}
        for e in range(1,13):
            if gcd(e,R)!=1:continue
            for n in range(1,22):
                reps=[]
                for m in range(1,32):
                    if gcd(m,R)!=1:continue
                    t=m*n-b
                    if t>0 and t%(a*e)==0:
                        v=t//(a*e)
                        if gcd(v,R)==1:reps.append((m,v))
                for m,v in reps:
                    for mp,vp in reps:
                        if mp==m:continue
                        assert gcd(n,a*e)==1
                        assert (mp-m)%(a*e)==0
                        k=(mp-m)//(a*e);z=mp*v
                        assert vp-v==k*n and m*vp==z+b*k
                        counts["forward"]+=1;c["forward"]+=1
                        if gcd(m,k)==gcd(mp,k)==1:
                            assert mask(a,k,R,m,mp)
                            er=(mp-m)//(a*k)
                            nr=(a*er*v+b)//m
                            assert (a*er*v+b)%m==0 and (er,nr)==(e,n)
                            counts["forward_inverse"]+=1
        for k in list(range(-6,0))+list(range(1,7)):
            Q=a*abs(k)*R
            for m in range(1,25):
                if gcd(m,Q)!=1:continue
                for mp in range(1,25):
                    if gcd(mp,Q)!=1:continue
                    pred=mask(a,k,R,m,mp)
                    direct=(mp-m)%(a*k)==0 and gcd((mp-m)//(a*k),R)==1
                    assert pred==direct,(a,b,k,R,m,mp)
                    counts["mask_equivalence"]+=1;c["mask"]+=1
                    if not pred:continue
                    e=(mp-m)//(a*k)
                    if e<=0:continue
                    for v in range(1,18):
                        if gcd(v,R)!=1:continue
                        zp=mp*v+b*k
                        if zp<=0 or zp%m!=0:continue
                        vp=zp//m
                        if gcd(vp,R)!=1:continue
                        numer=a*e*v+b
                        if numer<=0:continue
                        assert numer%m==0
                        n=numer//m
                        assert m*n==a*e*v+b and mp*n==a*e*vp+b
                        assert vp-v==k*n and gcd(n,a*e)==1
                        counts["independent_inverse"]+=1;c["inverse"]+=1
        for p in (3,5,7,11,13):
            Z={(m,n) for m in range(p) for n in range(p) if m*n%p==0}
            B={(m,n) for m in range(p) for n in range(p) if (m*n-b)%p==0}
            assert len(Z)==2*p-1
            if b%p==0:
                assert Z==B
                # ratio of good-pair probabilities to the b-unit baseline
                assert (p-1)**2*(p-2)==(p*p-3*p+2)*(p-1)
            else:
                assert len(B)==p-1 and not Z&B
                assert len(Z|B)==3*p-2
            counts["local_pairs"]+=1
        by_pair[key]=c
assert all(str((2 if h%2 else 1))+","+str(-h) in by_pair for h in bs)
assert all(counts.values())
print("PASS general_parametrisation: " + json.dumps(counts, sort_keys=True))
