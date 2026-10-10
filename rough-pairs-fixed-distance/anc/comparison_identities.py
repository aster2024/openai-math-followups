"""Exact finite checks for interval decoding and Walsh correction."""
from fractions import Fraction as F
from itertools import product, combinations

cases = 0
# Dyadic-prefix disjunction: disjoint maximal binary subtrees of an interval.
def blocks(lo,hi,B):
    result=[]
    while lo <= hi:
        width = (lo & -lo) if lo else 1 << B
        while width > hi-lo+1: width //= 2
        result.append((lo,width))
        lo += width
    return result

for B in range(1,7):
    length=1<<B
    for lo in range(length):
        for hi in range(lo,length):
            encoded=blocks(lo,hi,B)
            assert len(encoded)<=2*B
            for x in (0,lo,hi,length-1,(lo+hi)//2):
                assert any(start<=x<start+width for start,width in encoded)==(lo<=x<=hi)
                cases += 1
    for s in range(2,19):
        decoded=[s*(2*k+1)//(2*length) for k in range(length)]
        assert all(0<=r<s for r in decoded)
        assert decoded==sorted(decoded)
        for r in range(s):
            positions=[i for i,value in enumerate(decoded) if value==r]
            if positions: assert positions==list(range(min(positions),max(positions)+1))
            cases += 1

# Low-order correction makes all selected marginals exactly uniform.
for B,t in ((3,1),(4,2),(5,2),(6,3)):
    cube=list(product((-1,1),repeat=B))
    weights=[F(1+(sum((i+1)*(x+1)//2 for i,x in enumerate(point))%7)) for point in cube]
    normalizer=sum(weights,F(0))/len(cube)
    f=[w/normalizer for w in weights]
    subsets=[S for size in range(1,t+1) for S in combinations(range(B),size)]
    def character(point,S):
        value=1
        for i in S: value *= point[i]
        return value
    hats={S:sum((value*character(point,S) for point,value in zip(cube,f)),F(0))/len(cube) for S in subsets}
    q=sum((abs(value) for value in hats.values()),F(0))
    a=q+F(1,100)
    correction=[sum((hats[S]*character(point,S) for S in subsets),F(0)) for point in cube]
    g=[(value-H+a)/(1+a) for value,H in zip(f,correction)]
    assert min(g)>=0 and sum(g,F(0))==len(cube)
    for S in subsets:
        assert sum((value*character(point,S) for point,value in zip(cube,g)),F(0))==0
        for bits in product((-1,1),repeat=len(S)):
            marginal=sum((value for point,value in zip(cube,g) if tuple(point[i] for i in S)==bits),F(0))/len(cube)
            assert marginal==F(1,2**len(S))
            cases += 1
    distance=sum((abs(x-y) for x,y in zip(f,g)),F(0))/(2*len(cube))
    assert distance <= (q+a*sum((abs(1-x) for x in f),F(0))/len(cube))/(2*(1+a))
    cases += 1
print('Finite comparison identities: %d cases, all equalities agree.' % cases)
