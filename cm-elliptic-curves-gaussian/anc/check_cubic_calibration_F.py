from pathlib import Path as _Path
_RESULTS = _Path(__file__).resolve().parent / 'results'
_RESULTS.mkdir(exist_ok=True)
def _quiet(*args, **kwargs):
    pass

"""Exact Jacobi calibration over actual residue types of Q(zeta_12).

Checks the primary-generator sign, both cubic embeddings, and the
Davenport--Hasse minus sign in relative residue degree two.  These are
additional to the universal Gauss--Jacobi checks in check_finite_gauss.py.
"""
from pathlib import Path
import json,math,time

started=time.time();reports=[]
def primes_of(n):
    out=[];p=2
    while p*p<=n:
        if n%p==0:
            out.append(p)
            while n%p==0:n//=p
        p+=1
    if n>1:out.append(n)
    return out
def Emul(a,b):
    return (a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0]-a[1]*b[1])
def Epow(a,n):
    out=(1,0)
    for _ in range(n):out=Emul(out,a)
    return out
for p in (5,7,11,13,17,19,23,31,37,43):
    degree=1 if p%12==1 else 2;q=p**degree
    nr=0 if degree==1 else next(a for a in range(2,p) if pow(a,(p-1)//2,p)==p-1)
    def mul(a,b):return ((a[0]*b[0]+nr*a[1]*b[1])%p,(a[0]*b[1]+a[1]*b[0])%p)
    def power(a,n):
        out=(1,0)
        while n:
            if n&1:out=mul(out,a)
            a=mul(a,a);n//=2
        return out
    els=[(a,b) for b in range(p if degree==2 else 1) for a in range(p)]
    omega=next(w for t in els[1:] if t!=(0,0)
               for w in [power(t,(q-1)//3)] if w!=(1,0))
    for omega in (omega,power(omega,2)):
        lookup={(1,0):0,omega:1,power(omega,2):2}
        chars={t:lookup[power(t,(q-1)//3)] for t in els if t!=(0,0)}
        counts=[0,0,0]
        for t in els:
            if t in ((0,0),(1,0)):continue
            one_minus=((1-t[0])%p,(-t[1])%p)
            counts[(chars[t]+chars[one_minus])%3]+=1
        J=(counts[0]-counts[2],counts[1]-counts[2])
        if p%3==2:
            pi=(-p,0);f=1
        else:
            assert omega[1]==0
            bound=2*math.isqrt(p)+2
            candidates=[(a,b) for a in range(-bound,bound+1) for b in range(-bound,bound+1)
                        if a*a-a*b+b*b==p and (a-1)%3==0 and b%3==0
                        and (a+b*omega[0])%p==0]
            assert len(candidates)==1,(p,omega,candidates)
            pi=candidates[0];f=degree
        expected=tuple(-v for v in Epow(pi,f))
        assert J==expected,(p,degree,omega,J,expected)
        assert J[0]**2-J[0]*J[1]+J[1]**2==q
        reports.append({'p':p,'residue_degree_over_Q':degree,'q':q,
                        'omega_residue':omega,'primary_E_generator':pi,
                        'relative_residue_degree_F_over_E':f,
                        'Jacobi_sum_E_coordinates':J,'identity':'J_F = -pi_E^f'})
r={'status':'PASS','elapsed_seconds':time.time()-started,'cases':reports,
   'scope':'Exact residue-field Jacobi calibration and conjugations. Not a global theta or zero-free certificate.'}
(_RESULTS / 'cubic_calibration_F.json').write_text(json.dumps(r,indent=2)+'\n')
_quiet(json.dumps({'status':r['status'],'cases':len(reports),'elapsed_seconds':r['elapsed_seconds']},indent=2))

print('check_cubic_calibration_F.py: PASS (see results/; scope in README.md)')
