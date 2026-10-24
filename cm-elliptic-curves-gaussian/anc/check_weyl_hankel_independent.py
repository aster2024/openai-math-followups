from pathlib import Path as _Path
_RESULTS = _Path(__file__).resolve().parent / 'results'
_RESULTS.mkdir(exist_ok=True)
def _quiet(*args, **kwargs):
    pass

"""Independent direct archimedean Jacquet/Hankel spot check.

The spherical inducing section is differentiated on the LOWER root,
independently of the upper/lower Lie identity used in the paper.  Angular integration
gives a Bessel-J Hankel integral, evaluated numerically by its zeros.
This is not an interval certificate or a proof of the global reflection.
"""
import argparse, json, time
from pathlib import Path
import mpmath as mp

ap=argparse.ArgumentParser()
ap.add_argument('--mode',type=int,required=True)
ap.add_argument('--rho',default='0.7')
ap.add_argument('--dps',type=int,default=40)
args=ap.parse_args()
mp.mp.dps=args.dps
started=time.time()
m=args.mode;rho=mp.mpf(args.rho);c=mp.mpf('2.7');nu=mp.mpf(4)/3
y=rho*mp.mpc(mp.mpf(3)/5,mp.mpf(4)/5)
assert m>=0
def f(r):
    return r**(m+1)*mp.besselj(m,c*r)/(rho*rho+r*r)**(nu+m)
integral=mp.quadosc(f,[0,mp.inf],zeros=lambda j:mp.besseljzero(m,j)/c)
lower_raw=(mp.j**m)*mp.rf(nu,m)*rho**nu*mp.conj(y)**m*2*mp.pi*integral
lower_normalized=(2/(mp.j*c))**m*lower_raw
W0=2*mp.pi*c**(nu-1)/(2**(nu-1)*mp.gamma(nu))*rho*mp.besselk(nu-1,c*rho)
expected=mp.conj(y)**m*W0
error=abs(lower_normalized/expected-1)
assert error<mp.mpf('1e-28'),(m,rho,error)
report={'status':'PASS, numerical only','mode':m,'rho':str(rho),'dps':args.dps,
        'relative_error':str(error),'direct_Hankel_integral':str(integral),
        'lower_normalized':str(lower_normalized),'expected_conjugate_mode':str(expected),
        'elapsed_seconds':time.time()-started,
        'scope':'Direct lower-root Jacquet integral versus bar(y)^m W0. No interval certification or global moment claim.'}
target=_RESULTS/('weyl_hankel_m%d_r%s.json'%(m,args.rho.replace('.','p')))
target.write_text(json.dumps(report,indent=2)+'\n')
_quiet(json.dumps(report,indent=2),flush=True)

print('check_weyl_hankel_independent.py: PASS (see results/; scope in README.md)')
