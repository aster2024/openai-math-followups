from pathlib import Path as _Path
_RESULTS = _Path(__file__).resolve().parent / 'results'
_RESULTS.mkdir(exist_ok=True)
def _quiet(*args, **kwargs):
    pass

"""Supplementary high-precision checks of the local Bessel normalization."""
import mpmath as m
import json,time
from pathlib import Path
m.mp.dps=45
started=time.time();results=[]
s=m.mpc('0.37','0.23');c=m.mpf('2.7')
for order in (0,1,2,3):
 a=m.mpf(order+1)/2
 # Substitution t=x^2/c^2, independently compared to the proposed gamma expression.
 integral=2*c**(-2*(s+a))*m.quad(lambda x:x**(2*(s+a)-1)*m.besselk(m.mpf(1)/3,x),[0,1,4,16,m.inf])
 predicted=2**(2*(s+a)-1)*c**(-2*(s+a))*m.gamma(s+a-m.mpf(1)/6)*m.gamma(s+a+m.mpf(1)/6)
 err=abs(integral/predicted-1)
 assert err<m.mpf('1e-28'),(order,err)
 results.append({'mode':order,'relative_error':str(err),'status':'PASS, not interval certified'})
report={'dps':m.mp.dps,'elapsed_seconds':time.time()-started,'checks':results,'limits':'Numerical spot checks only; the identities are proved analytically in the paper.'}
(_RESULTS / 'archimedean.json').write_text(json.dumps(report,indent=2)+'\n')
_quiet(json.dumps(report,indent=2))

print('check_archimedean.py: PASS (see results/; scope in README.md)')
