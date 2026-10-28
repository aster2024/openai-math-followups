#!/usr/bin/env python3
"""Exhaust the unused-input and constant-gate counting conventions (Section 2.1)."""
import itertools

def contraction(n, kind, pin):
    # Logical edges x_0,...,x_{n-1},y. Each unused x has two (1,1) endpoints.
    # For a used x_0 there is one (1,1) endpoint and the functional gate endpoint.
    factors=[]
    for i in range(n):
        factors.append(((i,),lambda a:1))
        if kind!='identity' or i!=0:
            factors.append(((i,),lambda a:1))
    if kind=='identity':
        factors.append(((0,n),lambda a:int(a[0]==a[1])))
    else:
        factors.append(((n,),lambda a:int(a[0]==int(kind))))
    if pin:
        factors.append(((n,),lambda a:int(a[0]==1)))
    total=0
    for assignment in itertools.product((0,1),repeat=n+1):
        product=1
        for scope,f in factors:
            product*=f(tuple(assignment[i] for i in scope))
        total+=product
    return total

cases=0
for n in range(5):
    for kind in ['0','1']+(['identity'] if n else []):
        assert contraction(n,kind,False)==2**n
        want=0 if kind=='0' else 2**n if kind=='1' else 2**(n-1)
        assert contraction(n,kind,True)==want
        cases+=1
assert contraction(2,'identity',True)==2
print(f'check_unused_inputs.py: PASS; {cases} functional/pinned cases; n=2, C=x_1 gives count 2')
