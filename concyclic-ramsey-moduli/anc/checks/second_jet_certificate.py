"""Exact order-two necessary conditions, with two determinant algorithms.

The seven-point family has parameters -2,0,2,x,y,-4-x-2*y,z.
The rational specialization is ONLY a test of rational-function expressions.
It is not a field specialization and not a non-Ramsey rational configuration.
"""
from fractions import Fraction as Q
from itertools import combinations_with_replacement
from math import prod
from pathlib import Path
import json


def matrix(nodes, jacobian):
    n, k = len(nodes), len(jacobian[0])
    gamma = [1/prod(nodes[i]-nodes[j] for j in range(n) if j != i) for i in range(n)]
    pairs = list(combinations_with_replacement(range(k),2))
    rows, labels = [], []
    for ell in range(n-5):
        for j,l in pairs:
            row=[sum(gamma[i]*nodes[i]**(ell+r)*
                     (jacobian[i][j]*(a==l)+jacobian[i][l]*(a==j))
                     for i in range(n)) for a in range(k) for r in range(3)]
            rhs=sum(4*gamma[i]*nodes[i]**ell*jacobian[i][j]*jacobian[i][l]
                    for i in range(n))
            rows.append(row+[rhs]);labels.append((ell,j,l))
    return rows, labels


def determinant_fraction(a):
    a=[list(map(Q,row)) for row in a]
    n=len(a);value=Q(1)
    for j in range(n):
        piv=next((i for i in range(j,n) if a[i][j]),None)
        if piv is None:return Q(0)
        if piv!=j:a[j],a[piv]=a[piv],a[j];value=-value
        divisor=a[j][j];value*=divisor
        for i in range(j+1,n):
            factor=a[i][j]/divisor
            for l in range(j+1,n):a[i][l]-=factor*a[j][l]
    return value


def determinant_bareiss(a):
    a=[row[:] for row in a];n=len(a);old=1;sign=1
    for j in range(n-1):
        piv=next((i for i in range(j,n) if a[i][j]),None)
        if piv is None:return 0
        if piv!=j:a[j],a[piv]=a[piv],a[j];sign=-sign
        pivot=a[j][j]
        for i in range(j+1,n):
            for l in range(j+1,n):
                numerator=a[i][l]*pivot-a[i][j]*a[j][l]
                assert numerator%old==0
                a[i][l]=numerator//old
        for i in range(j+1,n):a[i][j]=0
        old=pivot
    return sign*a[-1][-1]


def ranks(a):
    a=[list(map(Q,row)) for row in a];ncol=len(a[0])-1;r=0
    for j in range(ncol):
        piv=next((i for i in range(r,len(a)) if a[i][j]),None)
        if piv is None:continue
        a[r],a[piv]=a[piv],a[r];pivot=a[r][j]
        a[r]=[x/pivot for x in a[r]]
        for i in range(len(a)):
            if i!=r:
                factor=a[i][j];a[i]=[x-factor*y for x,y in zip(a[i],a[r])]
        r+=1
    inconsistent=any(row[-1] and not any(row[:-1]) for row in a)
    return r,r+int(inconsistent),not inconsistent


def main():
    nodes=list(map(Q,[-2,0,2,-3,-1,1,3]))
    jacobian=[[0,0,0],[0,0,0],[0,0,0],[1,0,0],[0,1,0],[-1,-2,0],[0,0,1]]
    a,labels=matrix(nodes,jacobian)
    minor=a[:10]
    value=determinant_fraction(minor)
    assert value==Q(1,30611001600000)
    integers=[[int(720*x) for x in row] for row in minor]
    assert all(Q(v,720)==x for row,rr in zip(integers,minor) for v,x in zip(row,rr))
    bareiss=determinant_bareiss(integers)
    assert Q(bareiss,720**10)==value
    assert ranks(a)==(9,10,False)
    # Scalar left-null certificate of the first 9 columns.
    dual=[(-1)**(i+9)*determinant_fraction([row[:9] for j,row in enumerate(minor) if j!=i])
          for i in range(10)]
    assert all(sum(dual[i]*minor[i][j] for i in range(10))==0 for j in range(9))
    assert sum(dual[i]*minor[i][9] for i in range(10))==value
    replay=[]
    for n in [6,7,8]:
        ns=list(map(Q,range(n)))
        jj=[[int(i==j) for j in range(n)] for i in range(n)]
        rows,_=matrix(ns,jj)
        ra,rb,consistent=ranks(rows)
        assert consistent==(n==6)
        replay.append({'n':n,'rank_A':ra,'rank_augmented':rb,'consistent':consistent})
    report={'family':['-2','0','2','x','y','-4-x-2*y','z'],
            'specialization':{'x':-3,'y':-1,'z':3},
            'row_labels':labels[:10], 'column_order':[(a,r) for a in range(3) for r in range(3)]+['rhs'],
            'integer_scale':720,'integer_minor':integers,
            'determinant':str(value),'integer_determinant':str(bareiss),
            'left_null_vector':[str(x) for x in dual],
            'rank_A':9,'rank_augmented':10,'generic_6_7_8_replay':replay,
            'scope':'The nonzero rational-function augmented minor proves impossibility for algebraically independent x,y,z; rational substituted nodes themselves remain Ramsey.'}
    Path('checks/second_jet_certificate.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: family augmented 10-by-10 minor =',value)
    print('PASS: independent integer Bareiss determinant =',bareiss)
    print('PASS: explicit left-null certificate and rank gap 9 -> 10.')
    print('PASS: direct second-order 6/7/8 cross-checks:',replay)


if __name__=='__main__':
    main()
