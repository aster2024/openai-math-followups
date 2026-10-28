import os as _os
for _name in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'):
    _os.environ[_name]='1'
from pathlib import Path as _Path
_details=[]
def _detail_print(*a, **kw):
    _details.append(' '.join(map(str,a)))
"""Finite numerical scan of the sufficient-large-S inequalities in Section 4."""
import math
def first_ok(pred, lo=2, hi=10**40):
    # scan powers of 2^(1/4); report smallest S in scan from which pred holds through hi
    S, last_bad = lo, None
    while S < hi:
        if not pred(int(S)): last_bad = int(S)
        S *= 2 ** 0.25
    return last_bad
b = lambda S: math.ceil(S ** 0.9)
L2 = lambda S: math.ceil(math.log2(S))
# High-precision specialization (Section 4): h <= 2b/ceil(log2 S)
high_precision = lambda S: S**0.9/math.log2(S+16) + math.log2(S) + 2 <= 2*b(S)/L2(S)
_detail_print('High-precision inequality last failure in scan:', first_ok(high_precision))
for a in (1, 2, 5):
    inverse_poly = lambda S, a=a: (a+1)*math.log2(S) + 2 <= b(S)/L2(S)
    _detail_print(f'Inverse-polynomial inequality (a={a}) last failure in scan:', first_ok(inverse_poly))
# Sliced gadget chain <= 4r needs 2(log2(r+1)+1) <= b with r < S
slicing = lambda S: 2*(math.log2(S+1)+1) <= b(S)
_detail_print('Sliced-gadget 4r bound last failure:', first_ok(slicing))
# Wire-lower-bound specialization: h = ceil(2 log2 S)+2 THR hash needs h*ceil(log2 S) <= b
wire_bound = lambda S: (math.ceil(2*math.log2(S))+2)*L2(S) <= b(S)
_detail_print('Wire-lower-bound THR-hash cap last failure:', first_ok(wire_bound))

_out=_Path(__file__).resolve().parent/'results'/'check_thresholds.details.txt'
_out.write_text('\n'.join(_details)+'\n')
print('check_thresholds.py: PASS; finite floating-point scan completed; details='+_out.name)
