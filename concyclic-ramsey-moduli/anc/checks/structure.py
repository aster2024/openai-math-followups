"""Independent exact checks of the new structural propositions."""
from fractions import Fraction as Q
from itertools import product
from math import prod
from collections import Counter
from pathlib import Path
import json
import sympy as sp


def rank(a):
    a=[list(map(Q,row)) for row in a]
    r=0
    for j in range(len(a[0])):
        pivot=next((i for i in range(r,len(a)) if a[i][j]),None)
        if pivot is None:continue
        a[r],a[pivot]=a[pivot],a[r]
        divisor=a[r][j];a[r]=[x/divisor for x in a[r]]
        for i in range(r+1,len(a)):
            factor=a[i][j];a[i]=[x-factor*y for x,y in zip(a[i],a[r])]
        r+=1
    return r


def main():
    ts=list(map(Q,[-2,0,2,-3,-1,1,3]))
    gamma=[1/prod(ts[i]-ts[j] for j in range(7) if i!=j) for i in range(7)]
    w=[[1,t,t*t] for t in ts]
    jac=[[0,0,0],[0,0,0],[0,0,0],[1,0,0],[0,1,0],[-1,-2,0],[0,0,1]]
    counts=Counter();containing=0
    for tail in product([-1,1],repeat=6):
        signs=(1,)+tail
        u=[[s*x for x in row] for s,row in zip(signs,w)]
        assert rank(u)==3
        for ell in [0,1]:
            assert all(sum(gamma[i]*ts[i]**ell*u[i][a]*u[i][b] for i in range(7))==0
                       for a in range(3) for b in range(3))
        combined=[w[i]+u[i] for i in range(7)]
        projection=rank(combined)-3
        counts[projection]+=1
        if rank([combined[i]+jac[i] for i in range(7)])==rank(combined):
            containing+=1
    assert counts=={0:1,1:7,2:21,3:35}
    assert containing==0

    # Universal algebraic-diagonal projector plus one bilinear determinant.
    t,u,eta,theta=sp.symbols('t u eta theta')
    T=sp.symbols('T1:4');U=sp.symbols('U1:4')
    rows=[[1,u,t,t*u]]+[[1,U[i],T[i],T[i]*U[i]] for i in range(3)]
    n=sp.det(sp.Matrix(rows))
    delta=sp.det(sp.Matrix([[1,x,x*x] for x in T]))
    projector=sp.Rational(1,2)+eta*theta/4
    numerator=sp.expand(-2*projector*(t-u)*n)
    def reduce_alg(expr):
        return sp.expand(sp.rem(sp.rem(sp.expand(expr),eta*eta-2,eta),theta*theta-2,theta))
    assert reduce_alg(projector*projector-projector)==0
    assert reduce_alg((eta-theta)*projector)==0
    assert reduce_alg(numerator.subs({t:eta,u:theta}))==0
    assert reduce_alg(numerator.subs({t:1+eta,u:1+theta}))==0
    assert sp.Poly(numerator,t,u).coeff_monomial(t*t*u*u)==0  # infinity
    for i in range(3):
        assert sp.expand(numerator.subs({t:T[i],u:U[i]}))==0
    diagonal=numerator.subs({**dict(zip(U,T)),theta:eta})
    assert sp.rem(sp.expand(diagonal+2*delta*(t-u)**2),eta*eta-2,eta)==0
    report={'sign_flips':64,'projection_dimension_counts':dict(counts),
            'family_velocity_space_contained_in_any_sign_flip_plus_W':False,
            'algebraic_plus_three_arbitrary_universal_projector_check':True,
            'non_domain_and_infinity':True}
    Path('checks/structure.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: 64 sign spaces, projection ranks 0/1/2/3 with counts 1/7/21/35.')
    print('PASS: Appendix E family velocity space lies in none of them at the test expression.')
    print('PASS: universal e*W*N certificate with sqrt(2) algebraic anchors and three free nodes.')


if __name__=='__main__':
    main()
