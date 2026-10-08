"""Exact CM good-prime traces, including the direction of the sextic twist."""
import json
from eisenstein import Field,mul,trace,norm,is_prime,split_generators,UNITS
Ds=[1,2,-2,3,5,16,-7,10,-432]
def ap(d,p):
 return -sum(0 if (r:=(x*x*x+d)%p)==0 else (1 if pow(r,(p-1)//2,p)==1 else -1) for x in range(p))
count=0
split_pairs=set();inert_pairs=set()
for pi in split_generators(199):
 p=norm(pi);F=Field(pi)
 for d in Ds:
  if d%p==0:continue
  j=F.index((4*d,0));psi=mul(UNITS[(-j)%6],pi)
  assert trace(psi)==ap(d,p),(d,pi,psi,ap(d,p))
  count+=1
  split_pairs.add((d,p))
for p in range(5,200):
 if not is_prime(p) or p%3!=2:continue
 for d in Ds:
  if d%p==0:continue
  assert ap(d,p)==0,(d,p)
  count+=1
  inert_pairs.add((d,p))
# E_16 is isomorphic to y^2+y=x^3, a good integral model at 2.
pts=1+sum((y*y+y-x*x*x)%2==0 for x in range(2) for y in range(2))
assert pts==3 and 2+1-pts==0
# Conductor-one type 6 example.
pi=(-2,-3);p3=mul(mul(pi,pi),pi);p6=mul(p3,p3)
assert p3==(19,18) and p6==(37,360) and trace(p6)==-286
report=json.dumps({'status':'PASS','exact_good_prime_checks':count,'split_rational_pairs':len(split_pairs),'inert_rational_pairs':len(inert_pairs),'distinct_rational_pairs':len(split_pairs|inert_pairs),'extra_good_2_checks':1,'rational_prime_bound':199,'D_values':Ds,'E16_good_2_points':pts,'eta6_pi3':p3,'eta6_pi6':p6,'eta6_trace_numerator':trace(p6),'scope':'exact finite traces; no zero-free inference; no wild-conductor table'},indent=2)
from pathlib import Path
r=Path(__file__).parent/'results';r.mkdir(exist_ok=True);(r/'cm.json').write_text(report);print(report)
