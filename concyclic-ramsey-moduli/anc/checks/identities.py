"""Symbolic identities and exact rational checks."""
from pathlib import Path
import json
from fractions import Fraction as Q
import sympy as sp


def main():
    s,t,u,v = sp.symbols('s t u v')
    a,b,c,d,e,f = sp.symbols('a b c d e f')
    nodes = [(a,b),(c,d),(e,f)]
    delta = sp.det(sp.Matrix([[x*x,x*y,y*y] for x,y in nodes]))
    bracket_product = (a*d-b*c)*(a*f-b*e)*(c*f-d*e)
    assert sp.expand(delta-bracket_product) == 0
    n_diag = sp.det(sp.Matrix([[s*u,s*v,t*u,t*v]]+[[x*x,x*y,x*y,y*y] for x,y in nodes]))
    assert sp.expand(n_diag-delta*(t*u-s*v)) == 0
    h=lambda x,y:sp.Matrix([x*x+y*y,x*x-y*y,2*x*y])
    assert sp.expand((h(s,t).T*sp.diag(-1,1,1)*h(u,v))[0]+2*(s*v-t*u)**2) == 0

    tests=[]
    for ts in [list(range(-3,4)),[Q(-5,2),Q(-4,3),Q(-1,7),Q(0),Q(2,5),Q(7,4),Q(9)]]:
        ts=[Q(x) for x in ts]
        gam=[1/sp.prod([ts[i]-ts[j] for j in range(7) if j!=i]) for i in range(7)]
        gam=[Q(x) for x in gam]
        assert [sum(gam[i]*ts[i]**k for i in range(7)) for k in range(7)] == [0]*6+[1]
        beta=[gam[i]*(1+ts[i]**2)**2 for i in range(7)]
        ps=[[Q(1),(1-x*x)/(1+x*x),2*x/(1+x*x)] for x in ts]
        vel=[]
        for x,p in zip(ts,ps):
            gx=sp.prod([x-ts[j] for j in range(3)])
            speed=2*Q(gx)/(1+x*x)
            vel.append([Q(0),-speed*p[2],speed*p[1]])
        S=[[sum(beta[i]*ps[i][a]*ps[i][b] for i in range(7)) for b in range(3)] for a in range(3)]
        M=[[sum(beta[i]*vel[i][a]*ps[i][b] for i in range(7)) for b in range(3)] for a in range(3)]
        K=[[sum(beta[i]*vel[i][a]*vel[i][b] for i in range(7)) for b in range(3)] for a in range(3)]
        assert S==[[0]*3 for _ in range(3)]
        assert M==[list(x) for x in zip(*M)]
        assert M[0]==[0]*3 and [row[0] for row in M]==[0]*3
        assert K[1][1]+K[2][2]==4
        tests.append({'parameters':[str(x) for x in ts],
                      'M':[[str(x) for x in row] for row in M],
                      'K':[[str(x) for x in row] for row in K],
                      'trace_spatial_K':4})
    assert sp.isprime(2147483629)
    report={'symbolic_delta':True,'symbolic_N_diagonal':True,'symbolic_circle_kernel':True,
            'exact_moment_tests':tests,'jet_modulus_prime':True,
            'scope':'Rational substitutions verify universal moment identities. They do not define a nonzero derivation on Q or assert that these rational configurations are non-Ramsey.'}
    Path('checks/identities.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: three universal homogeneous polynomial identities.')
    print('PASS: two rational specializations of the seven-point moment identities, trace exactly 4.')
    print('PASS: original jet modulus is prime.')


if __name__=='__main__':
    main()
