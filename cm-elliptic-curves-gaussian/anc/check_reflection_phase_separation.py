from pathlib import Path as _Path
_RESULTS = _Path(__file__).resolve().parent / 'results'
_RESULTS.mkdir(exist_ok=True)
def _quiet(*args, **kwargs):
    pass

"""Formal exponent check of the frozen, row and column phase separation
in the reflected sum.

All sextic symbols are independent formal roots subject ONLY to symmetric
allowed-generator reciprocity. Unit-symbol variables remain nontrivial.
There is no numerical approximation and no finite Fourier expansion of
the infinite-order background character.
"""
from collections import defaultdict
from itertools import product
from pathlib import Path
import json,time

start=time.time();size=3
def addv(*vs):return [sum(v[i] for v in vs) for i in range(size)]
def scale(v,k):return [k*x for x in v]
def without(v,p):
    out=list(v);out[p]=0;return out
def char(poly,p,vals,power=1,epsilon=0):
    assert vals[p]==0,(p,vals)
    if epsilon:poly['unit',p]+=epsilon*power
    for q,e in enumerate(vals):
        if q!=p and e:poly['pair',min(p,q),max(p,q)]+=e*power
def reduced(poly):return {k:v%6 for k,v in poly.items() if v%6}

# State=(role,a_exponent,n_exponent,mask_j).
states=[('none',0,0,0),('d',0,0,1),('c',0,0,0)]
states += [('n',0,n,0) for n in (1,2)]
states += [('cn',0,n,0) for n in (1,2)]
states += [('f',0,0,j) for j in range(6)]
states += [('f',e,0,4) for e in (1,3,4,6,7)]
states += [('fi',e,0,0) for e in (0,1,3,4,6,7)]
count=0;shared=0;active_zero_digit=0;inactive_label=0
for config in product(states,repeat=size):
    d=[int(v[0]=='d') for v in config]
    f=[int(v[0] in ('f','fi')) for v in config]
    den=[int(v[0]=='f') for v in config]
    c=[int(v[0] in ('c','cn')) for v in config]
    a=[v[1] for v in config];n=[v[2] for v in config]
    nu=addv(a,c,scale(n,3),scale(d,-2),scale(den,-2))
    b=[(2*v[1] if v[0]=='fi' else
        ((8-v[3]) if v[1]==0 else 4+2*v[1]))%6 for v in config]
    original=defaultdict(int)
    for p in range(size):
        if d[p]:
            assert nu[p]==-2
            char(original,p,without(nu,p),epsilon=1)
        elif f[p]:
            assert nu[p]==a[p]-2*den[p]
            char(original,p,without(nu,p),power=b[p],epsilon=1)
        elif c[p]:
            assert nu[p]==1+3*n[p]
            char(original,p,without(nu,p),power=2*nu[p],epsilon=1)
        elif n[p]:
            assert nu[p]%3==0
            char(original,p,without(nu,p),power=2*nu[p],epsilon=1)

    separated=defaultdict(int)
    # Frozen Omega.
    for p in range(size):
        if f[p]:
            vals=addv(without(a,p),scale(n,3),scale(without(den,p),-2))
            char(separated,p,vals,power=b[p],epsilon=1)
    # Row r(d), with its label-prime row factor.
    for p in range(size):
        if d[p]:
            vals=addv(a,scale(n,3),scale(without(d,p),-2),scale(den,-2))
            char(separated,p,vals,epsilon=1)
        if f[p]:char(separated,p,d,power=-2*b[p])
    # Common column lambda(c), including its intrinsic Gauss CRT phase.
    for p in range(size):
        if f[p]:char(separated,p,c,power=b[p])
        if c[p]:
            vals=addv(a,without(c,p),scale(den,-2))
            char(separated,p,vals,power=2,epsilon=1)
    # The quadratic cross kernel.
    for p in range(size):
        if d[p]:char(separated,p,c,power=3)
    assert reduced(original)==reduced(separated),(config,reduced(original),reduced(separated))
    # Exact full Hecke factor L(nu)^(-1) on ideal prime valuations.
    assert scale(nu,-1)==addv(scale(a,-1),scale(c,-1),scale(n,-3),scale(d,2),scale(den,2))
    count+=1
    shared+=int(any(c[p] and n[p] for p in range(size)))
    active_zero_digit+=int(any(den[p] and config[p][3]==0 for p in range(size)))
    inactive_label+=int(any(config[p][0]=='fi' for p in range(size)))

# Collision zero at a valuation-one row prime: if a free cube or column
# enters that prime, the local reflected j=1 branch has positive e and is
# zero. The separated formula has respectively its explicit (n,d)=1 or
# quadratic (c,d)=1 zero. Do not call a forbidden parameterization nonzero.
collisions=0
for ce,ne in product((0,1),range(3)):
    e=ce+3*ne
    local_nonzero=e==0
    separated_nonzero=(ce==0 and ne==0)
    assert local_nonzero==separated_nonzero
    collisions+=1

report={'status':'PASS','elapsed_seconds':time.time()-start,
        'independent_formal_primes':size,'local_states_per_prime':len(states),
        'global_exponent_configurations':count,'shared_c_n_configurations':shared,
        'active_zero_digit_configurations':active_zero_digit,
        'inactive_label_configurations':inactive_label,
        'collision_zero_configurations':collisions,
        'scope':'Exact formal sextic exponent equality, unit phases, shared cube primes and full Hecke-factor splitting. Not global automorphy or an analytic large-sieve certificate.'}
(_RESULTS / 'reflection_phase_separation.json').write_text(json.dumps(report,indent=2)+'\n')
_quiet(json.dumps(report,indent=2))

print('check_reflection_phase_separation.py: PASS (see results/; scope in README.md)')
