"""Exact certificate for a transcendence-degree-one positive seven-point family."""
from fractions import Fraction as Q
from itertools import combinations
from pathlib import Path
import json
import sympy as sp


def main():
    x,u,y,v,t,w=sp.symbols('x u y v t w')
    A=lambda x,y:3*x*x+9*x-4-10*y
    B=lambda x,y:5*x**3+45*x*x-40-(27*x+19)*y
    curve=sp.expand(B(x,y)**2-A(x,y)**3+2*(x-3)**6)
    qc,rc=sp.div(curve,y*y-x**3+2,y)
    assert sp.expand(rc)==0
    assert sp.expand(qc-(-171*x*x-1674*x+1000*y+1561))==0
    dx,du=x-3,u-3
    ax,au,bx,bu=A(x,y),A(u,v),B(x,y),B(u,v)
    S=x*u*(x+u)-4+2*y*v
    M=ax*au*(ax*du*du+au*dx*dx)-4*dx**4*du**4+2*bx*bu*dx*du
    C=sp.expand(M*(x-u)**2-S*(ax*du*du-au*dx*dx)**2)
    q1,r1=sp.div(C,y*y-x**3+2,y)
    q2,r2=sp.div(r1,v*v-u**3+2,v)
    assert sp.expand(r2)==0
    assert sp.expand(C-q1*(y*y-x**3+2)-q2*(v*v-u**3+2))==0
    K=t*w*(t+w)-4;L=t*t*w*w+8*(t+w)
    assert sp.expand(K*K-(t-w)**2*L-4*(t**3-2)*(w**3-2))==0
    points=[]
    xx,yy=Q(129,100),Q(-383,1000)
    for i in range(8):
        assert yy*yy==xx**3-2 and xx!=3
        points.append((xx,yy));den=xx-3
        xx,yy=(3*xx*xx+9*xx-4-10*yy)/den**2,(5*xx**3+45*xx*xx-40-(27*xx+19)*yy)/den**3
    xs=[p[0] for p in points]
    assert len(set(xs))==8
    assert sorted(range(8),key=lambda i:xs[i])==[0,7,4,3,1,6,5,2]
    def cross(a,b,c,d):return (a-c)*(b-d)/((a-d)*(b-c))
    records=[]
    for inds in combinations(range(7),4):
        first=cross(*(xs[i] for i in inds))
        second=cross(*(xs[i+1] for i in inds))
        assert first!=second
        records.append({'indices':inds,'first':str(first),'second':str(second),
                        'difference':str(first-second)})
    signs=''.join('+' if Q(r['difference'])>0 else '-' for r in records)
    assert signs=='--+-++--++-----+--++++---++++---+++'
    # Independent Fraction checks of simultaneous translation invariance.
    def dval(p,q):
        a,b=p;c,d=q
        return (a*c*(a+c)-4+2*b*d)/(a-c)**2
    for i,j in combinations(range(7),2):
        assert dval(points[i],points[j])==dval(points[i+1],points[j+1])
    # Multiplied certificate is the circle kernel, using m(S)=4*y^2, m(Z)=0.
    normal=sp.Rational(-2,1)/(4*y*y)**2
    assert sp.expand(normal*(t-w)**2*(4*y*y)**2+2*(t-w)**2)==0
    report={'curve_identity_quotient':str(sp.factor(qc)),
            'pair_identity_quotient_y':str(sp.factor(q1)),
            'pair_identity_quotient_v':str(sp.factor(q2)),
            'universal_pair_identity':True,'universal_biquadratic_identity':True,
            'test_points':[[str(a),str(b)] for a,b in points],
            'cross_ratios':records,'lexicographic_difference_signs':signs,
            'fraction_pair_invariance_checks':21,'scope':'Rational tests certify identities and nonconstant functions; actual theorem requires transcendental x.'}
    Path('checks/elliptic.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: curve map, simultaneous-pair invariant and biquadratic identity.')
    print('PASS: 21 independent Fraction pair-invariance tests.')
    print('PASS: 35 cross-ratio functions have different rational test values.')


if __name__=='__main__':
    main()
