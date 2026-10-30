#!/usr/bin/env python3
"""Exact polynomial identities, rational parameters and cubic examples."""
import json
from fractions import Fraction as F
from pathlib import Path

import sympy as s

ROOT = Path(__file__).resolve().parent


def main():
    t, a, b, c, d, v = s.symbols('t a b c d v')
    A, B = 9*a*c-3*b*b, 2*b**3-9*a*b*c+27*a*a*d
    assert s.expand(27*a*a*(a*t**3+b*t*t+c*t+d)-((3*a*t+b)**3+A*(3*a*t+b)+B)) == 0
    assert s.expand(4*a*(a*t*t+b*t+c)-((2*a*t+b)**2+4*a*c-b*b)) == 0
    x,y=s.symbols('x y')
    assert s.expand(x**3+y**3+A*(x+y)-(x+y)*(x*x-x*y+y*y+A)) == 0
    assert s.expand(2*(x*x-x*y+y*y)-(x-y)**2-x*x-y*y) == 0
    assert F(1,2)-F(38,167)/F(9,2) == F(1351,3006)
    kappa = F(899,2000)
    dk=F(1,2)-kappa
    scalar=F(5,2)*dk/(1+10*dk)
    assert F(1351,3006)<kappa<F(9,20)
    assert scalar<F(1,8)
    assert F(9,2)*dk<F(38,167)
    out={'identities': 'all expanded differences exactly zero',
         'kappa_7_8': str(kappa), 'scalar_threshold': str(scalar),
         'raw_threshold': str(F(9,2)*dk), 'raw_density_cutoff': str(F(38,167))}
    # A genuine zero branch, whose size is finite only after Q is fixed.
    Q=lambda u:(u-101)**3+5000000
    pairs=[(u,202-u) for u in range(1,202)]
    assert all(Q(u)+Q(w)==10000000 for u,w in pairs)
    out['fixed_cubic_zero_branch']={'polynomial':'(t-101)^3+5000000','ordered_positive_pairs':len(pairs),'sum':10000000}
    # Exact moving-coefficient family: the large multiplicity is its zero branch.
    out['moving_cubic_examples']=[]
    for m in [3,10,101]:
        vals=[2*(2*t-m-1)**3+6*m**3 for t in range(1,m+1)]
        assert min(vals)>=4*m**3 and max(vals)<=8*m**3
        assert all(z%2==0 for z in vals) and len(set(vals))==m
        assert all(vals[u-1]+vals[m-u]==12*m**3 for u in range(1,m+1))
        out['moving_cubic_examples'].append({'M':m,'X':8*m**3,'pair_count':m,'all_even_and_distinct':True})
    (ROOT / 'results').mkdir(parents=True, exist_ok=True)
    (ROOT / 'results/exact_checks.json').write_text(json.dumps(out,indent=2)+'\n')
    print('PASS exact_checks: polynomial identities, rational parameters, fixed and moving cubic examples')


if __name__=='__main__':
    main()
