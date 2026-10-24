from pathlib import Path as _Path
_RESULTS = _Path(__file__).resolve().parent / 'results'
_RESULTS.mkdir(exist_ok=True)
def _quiet(*args, **kwargs):
    pass

"""Exact local checks only, in cyclotomic integer arithmetic."""
from pathlib import Path
import sympy as s
import json,time
started=time.time();z=s.symbols('z');reports=[]
for p,degree in [(13,1),(5,2),(7,2),(11,2),(37,1)]:
 q=p**degree
 nr=next((a for a in range(2,p) if pow(a,(p-1)//2,p)==p-1),None) if degree==2 else 0
 els=[(a,b) for b in range(p if degree==2 else 1) for a in range(p)]
 def mul(x,y):return ((x[0]*y[0]+nr*x[1]*y[1])%p,(x[0]*y[1]+x[1]*y[0])%p)
 def power(x,n):
  r=(1,0)
  while n:
   if n&1:r=mul(r,x)
   x=mul(x,x);n//=2
  return r
 factors=list(s.factorint(q-1));g=next(x for x in els[1:] if x!=(0,0) and all(power(x,(q-1)//int(l))!=(1,0) for l in factors))
 logs={};x=(1,0)
 for j in range(q-1):logs[x]=j;x=mul(x,g)
 assert len(logs)==q-1
 M=6*p;phi=s.Poly(s.cyclotomic_poly(M,z),z,domain=s.ZZ)
 def poly(exponents):
  d={}
  for e in exponents:d[(int(e)%M,)]=d.get((int(e)%M,),0)+1
  return s.Poly.from_dict(d,z,domain=s.ZZ).rem(phi)
 def pmul(a,b):return (a*b).rem(phi)
 one=s.Poly(1,z,domain=s.ZZ);zero=s.Poly(0,z,domain=s.ZZ)
 def phase(e):return poly([e])
 def trace(x):return (degree*x[0])%p
 G={j:poly(p*j*lx+6*trace(xx) for xx,lx in logs.items()) for j in range(6)}
 J=poly(p*2*(lx+logs[((1-xx[0])%p,(-xx[1])%p)]) for xx,lx in logs.items() if xx!=(1,0))
 assert pmul(pmul(G[2],G[2]),G[2])==J.mul_ground(q)
 assert pmul(G[2],G[4])==one.mul_ground(q)
 assert pmul(G[1],G[4])==pmul(phase(-p*logs[(4%p,0)]),pmul(G[2],G[3]))
 assert pmul(G[3],G[3])==one.mul_ground(q)
 for j in range(1,6):assert pmul(G[j],G[(6-j)%6])==one.mul_ground(q)
 ntested=0
 if q<=25:
  for j in range(6):
   base=poly(p*(4-j)*lv+6*trace(power(v,q-2)) for v,lv in logs.items())
   for t,lt in logs.items():
    actual=pmul(phase(4*p*lt),poly(p*(4-j)*lv+6*trace(mul(t,power(v,q-2))) for v,lv in logs.items()))
    assert actual==pmul(phase((8-j)*p*lt),base),(q,j,t)
    ntested+=1
 for j in range(6):
  total=poly(p*(4-j)*lv for lv in logs.values())
  assert total==(one.mul_ground(q-1) if j==4 else zero)
 reports.append({'p':p,'degree':degree,'q':q,'generator':g,'Gauss_Jacobi':'exact PASS','sextic_duplication':'exact PASS','quadratic_sign_square':'exact PASS','active_e0_unit_checks':ntested,'positive_e_support':'exact PASS'})
 _quiet('PASS q =',q,flush=True)
report={'method':'Z[z]/Phi_(6p)(z), exact integer polynomial reduction','elapsed_seconds':time.time()-started,'fields':reports,'limits':'Finite local checks, not a global or zero-free certificate.'}
(_RESULTS / 'finite_gauss.json').write_text(json.dumps(report,indent=2)+'\n')
_quiet(json.dumps(report,indent=2))

print('check_finite_gauss.py: PASS (see results/; scope in README.md)')
