#!/usr/bin/env python3
"""Independent finite checks of local conditions and counting-window conversion."""

from math import gcd
from fractions import Fraction
import json

def rad(n):
    n=abs(n);r=1;p=2
    while p*p<=n:
        if n%p==0:
            r*=p
            while n%p==0:n//=p
        p+=1
    return r*n

def squarefree(n):
    p=2
    while p*p<=n:
        if n%(p*p)==0:return False
        p+=1
    return True

def prime(n):
    if n<2:return False
    p=2
    while p*p<=n:
        if n%p==0:return False
        p+=1
    return True

c={"good_form_units":0,"even_form_obstruction":0,"common_divisor_obstruction":0,
   "root_pairs":0,"window_conversion":0,"squarefree_conversion":0,"local_product_ratios":0}
for a in range(1,9):
    for b in range(-24,25):
        if b==0:continue
        R=rad(2*a*b)
        for u in range(1,100,2):
            if gcd(u,R)!=1 or a*u+b<=0:continue
            value=a*u+b
            if gcd(a,b)==1 and (a+b)%2==1:
                assert gcd(value,R)==1
                c["good_form_units"]+=1
            if gcd(a,b)==1 and (a+b)%2==0:
                assert value%2==0
                assert not prime(value) or value==2
                c["even_form_obstruction"]+=1
            if gcd(a,b)>1:
                assert value%gcd(a,b)==0
                c["common_divisor_obstruction"]+=1
        for d in (3,5,7,9,15,25,35,49):
            if gcd(d,a*b)!=1:continue
            count=sum((m*n-b)%d==0 for m in range(d) for n in range(d))
            phi=sum(gcd(m,d)==1 for m in range(d))
            assert count==phi
            c["root_pairs"]+=1

for p in (3,5,7,11,13,17,19):
    b_good=1
    zero={(m,n) for m in range(p) for n in range(p) if m*n%p==0}
    target={(m,n) for m in range(p) for n in range(p) if (m*n-b_good)%p==0}
    baseline=Fraction(p*p-len(zero|target),p*p)
    bad_shift_factor=Fraction(p*p-len(zero),p*p)
    assert bad_shift_factor/baseline==Fraction(p-1,p-2)
    # For p | a the banned event is dropped and only the roughness condition remains;
    # its good-pair factor is bad_shift_factor itself.
    c["local_product_ratios"]+=1

for h in range(-50,51):
    if h==0:continue
    a=2 if h%2 else 1
    b=-h
    for X in (1000,2000,5000):
        x=Fraction(X-abs(h),2*a)
        lo=(x.numerator+x.denominator-1)//x.denominator
        hi=(2*x).numerator//(2*x).denominator
        for u in range(lo,hi+1):
            if u%2==0:continue
            p=a*u-h
            assert p<=X and p+h==a*u and p+h>0
            c["window_conversion"]+=1
            if squarefree(u):
                assert squarefree(p+h)
                c["squarefree_conversion"]+=1
assert all(c.values())
print("PASS general_local_conditions: " + json.dumps(c, sort_keys=True))
