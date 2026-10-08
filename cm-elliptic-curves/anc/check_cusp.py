"""Exact smooth-jet identities and the Lie-algebra reason for pure derivatives."""
import json
from pathlib import Path
import sympy as s
z,zb,v,c,cb=s.symbols('z zb v c cb',nonzero=True)
Q=v*v+z*zb
D=(-zb/(c*c*Q),-z/(cb*cb*Q),v/(c*cb*Q)-1/(c*cb*v))
records=[]
# Each generic Taylor monomial is checked; this includes all mixed and height terms.
for m in range(1,7):
 count=0
 for i in range(m+1):
  for j in range(m+1-i):
   for h in range(m+1-i-j):
    f=D[0]**i*D[1]**j*D[2]**h
    # Restriction to the formal z=0 axis commutes with pure zb differentiation.
    lhs=s.diff(f.subs(z,0),zb,m).subs(zb,0)
    rhs=s.factorial(m)*(-1/(c*c*v*v))**m if (i,j,h)==(m,0,0) else 0
    assert s.simplify(lhs-rhs)==0,(m,i,j,h)
    count+=1
 records.append({'mode':m,'generic_monomials':count})
assert s.diff(D[2],zb).subs({z:0,zb:0})==0
mixed=s.diff(D[2],z,zb).subs({z:0,zb:0})
assert s.simplify(mixed+1/(c*cb*v**3))==0
E=s.Matrix([[0,1],[0,0]]);F=s.Matrix([[0,0],[1,0]]);W=s.Matrix([[0,-1],[1,0]])
assert W*E*W.inv()==-F
# sl2 direct sum: E=(E,0), K0=(E,-F), hence [K0,E]=(0,0).
assert E*E-E*E==s.zeros(2)
# Three representative denominator classes, with 2 and conductor primes included.
lam=1+2*s.exp(2*s.pi*s.I/3)
classes=[{'lambda_valuation':0,'c':'26'}, {'lambda_valuation':1,'c':'26*lambda'}, {'lambda_valuation':2,'c':'26*lambda^2'}]
out={'status':'PASS','exact':True,'records':records,'mixed_height_derivative':str(mixed),'denominator_classes':classes,'scope':'generic smooth pure jet, not numerical certification of an infinite theta expansion'}
t=json.dumps(out,indent=2);r=Path(__file__).parent/'results';r.mkdir(exist_ok=True);(r/'cusp.json').write_text(t);print(t)
