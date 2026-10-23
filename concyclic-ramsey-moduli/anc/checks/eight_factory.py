"""Exact checks for two projective algebraic groups and the eight-node lemma."""
from structure import rank
from fractions import Fraction as Q
from itertools import product
from math import prod
from collections import Counter
import sympy as sp
import json
from pathlib import Path


def main():
    ts=list(map(Q,range(-3,5)))
    gamma=[1/prod(ts[i]-ts[j] for j in range(8) if j!=i) for i in range(8)]
    w=[[1,t,t*t] for t in ts]
    counts=Counter()
    for tail in product([-1,1],repeat=7):
        signs=(1,)+tail
        u=[[signs[i]*x for x in w[i]] for i in range(8)]
        for ell in range(3):
            assert all(sum(gamma[i]*ts[i]**ell*u[i][a]*u[i][b] for i in range(8))==0
                       for a in range(3) for b in range(3))
        assert rank([u[i]+[ts[i]*x for x in u[i]] for i in range(8)])==4
        counts[rank([w[i]+u[i] for i in range(8)])-3]+=1
    assert counts=={0:1,1:8,2:28,3:91}
    a,b,c,A,B,C,s,t,u,v=sp.symbols('a b c A B C s t u v')
    left=sp.Matrix([[a,-c],[-b,1]])
    right=sp.Matrix([[A,-C],[-B,1]])
    vector_l=left*sp.Matrix([s,t]);vector_r=right*sp.Matrix([u,v])
    graph=sp.det(sp.Matrix.hstack(vector_l,vector_r))
    diagonal=graph.subs({A:a,B:b,C:c})
    wedge=s*v-t*u
    assert sp.expand(diagonal-(a-b*c)*wedge)==0
    old=[(1,0),(1,1),(1,-1),(0,1)]
    for p,q in old:
        zl=(p+c*q,b*p+a*q);zr=(p+C*q,B*p+A*q)
        assert sp.expand(graph.subs({s:zl[0],t:zl[1],u:zr[0],v:zr[1]}))==0
        assert sp.expand(wedge.subs({s:p,t:q,u:p,v:q}))==0
    report={'eight_sign_spaces':128,'projection_dimension_counts':dict(counts),
            'eight_node_U_plus_TU_dimension':4,
            'symbolic_two_group_graph_certificate':True,
            'family':'{0,1,-1,infinity} union g({0,1,-1,infinity}); g=[[1,c],[b,a]]'}
    Path('checks/eight_factory.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: 128 eight-node sign spaces and dimension-4 U+TU.')
    print('PASS: universal two-projective-group eight-point certificate.')


if __name__=='__main__':
    main()
