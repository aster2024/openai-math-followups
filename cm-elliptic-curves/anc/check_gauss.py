"""75-digit Gauss identities, exact Jacobi sums, and every active/inactive local branch."""
import json
import mpmath as mp
from eisenstein import Field,mul,conjugate,norm,UNITS
mp.mp.dps=75
zeta=mp.exp(2j*mp.pi/6)
def value(x):return mp.mpf(x[0])+x[1]*mp.exp(2j*mp.pi/3)
records=[]
for pi in [(-2,-3),(1,3),(4,3),(-5,-6),(-5,0),(-11,0)]:
 F=Field(pi);q=F.q
 def chi(x,j):
  k=F.index(x)
  return mp.mpc(0) if k is None else zeta**((j*k)%6)
 def additive(x):
  t=mul(x,conjugate(pi));return mp.exp(2j*mp.pi*t[1]/q)
 def gam(j):return mp.fsum(chi(x,j)*additive(x) for x in F.elements)/mp.sqrt(q)
 g={j:gam(j) for j in [1,2,3,4,5]}
 al=value(pi)/mp.sqrt(q);G=mp.conj(chi((4,0),1))*g[3]
 errs=[abs(g[2]**3+al),abs(g[1]*g[2]+al*G),abs(-g[5]-chi((-1,0),1)/G*mp.conj(al)*g[2])]
 J=F.jacobi(2,2);assert J==(-pi[0],-pi[1]),(pi,J)
 # Exact Jacobi J(chi^2,chi^3)=-pi*conj(chi(4)).
 j23=F.jacobi(2,3);idx=F.index((4,0));target=mul((-pi[0],-pi[1]),UNITS[(-idx)%6]);assert j23==target
 worst=max(errs)
 for j in range(6):
  C={h:mp.fsum(chi(x,j)*mp.conj(additive(F.multiply(h,x))) for x in F.elements)/q for h in F.elements}
  assert abs(C[(0,0)]-(1-mp.mpf(1)/q if j==0 else 0))<mp.mpf('1e-65')
  for x in F.elements:
   lhs=mp.fsum(C[h]*chi(h,-2)*additive(F.multiply(F.power(h,q-2),x)) for h in F.elements if h!=(0,0))
   if j not in [0,4]:
    rhs=chi((-1,0),j)*g[j]*g[(j+2)%6]*chi(x,-j-2)
   elif j==4:rhs=g[4]/mp.sqrt(q)*(-1+q*(x==(0,0)))
   else:rhs=-g[2]/mp.sqrt(q)*chi(x,-2)
   worst=max(worst,abs(lhs-rhs))
 assert worst<mp.mpf('1e-65'),(pi,worst)
 records.append({'pi':pi,'norm':q,'jacobi_22':J,'jacobi_23':j23,'max_error':mp.nstr(worst,12)})
report=json.dumps({'status':'PASS','precision':75,'scope':'six small split/inert primes; all j and x; sigma=epsilon=1','records':records},indent=2)
from pathlib import Path
r=Path(__file__).parent/'results';r.mkdir(exist_ok=True);(r/'gauss.json').write_text(report);print(report)
