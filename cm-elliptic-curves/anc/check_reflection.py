"""60-digit Bessel/Mellin normalization and one-mode cusp reflection.
Run one case per process: --case 0,1,2. Each case corresponds to one lambda-valuation class.
This checks the analytic reflection identity and its exact scalar; it is not an interval certificate
for a truncated full theta series and does not establish any zero-free region.
"""
import argparse,json,time,signal
from pathlib import Path
import mpmath as mp
ap=argparse.ArgumentParser();ap.add_argument('--case',type=int,choices=[0,1,2],default=0);args=ap.parse_args()
signal.alarm(28)
mp.mp.dps=60
started=time.monotonic();m=[1,2,4][args.case];omega=mp.exp(2j*mp.pi/3);base=2*(4+3*omega);c=base*(1j*mp.sqrt(3))**args.case
pi=4+3*omega
ell=pi/9 if args.case<2 else pi/(1j*mp.sqrt(3))**3;q=abs(c)**2;s=mp.mpc(mp.mpf(3)/5,mp.mpf(1)/7)
al=lambda z:z/abs(z)
G=lambda w:mp.gamma(w+m/2-mp.mpf(1)/6)*mp.gamma(w+m/2+mp.mpf(1)/6)
# Standard Bessel integral, independently integrated.
raw=mp.quad(lambda u:u**(2*s+m-1)*mp.besselk(mp.mpf(1)/3,4*mp.pi*abs(ell)*u),[0,mp.mpf('0.1'),1,mp.inf])
closed=2**(2*s+m-2)*(4*mp.pi*abs(ell))**(-2*s-m)*G(s)
err1=abs(raw-closed)/abs(closed)
# The differentiated single Fourier mode at inverse-cusp height, evaluated directly.
def source(v):
 u=1/(q*v)
 return (-1/(c*c*v*v))**m*(2j*mp.pi*ell)**m*u*mp.besselk(mp.mpf(1)/3,4*mp.pi*abs(ell)*u)*v**(2*s+m-2)
lhs=mp.quad(source,[0,1/q,1,mp.inf])
Jplus=(1j)**m/(4*(2*mp.pi)**(2*(1-s)))*G(1-s)*al(ell)**m*abs(ell)**(-2*(1-s))
rhs=(-1)**m*al(c)**(-2*m)*q**(1-2*s)*Jplus
err2=abs(lhs-rhs)/abs(rhs)
# Constant simplification entering the full masked formula.
scalar=(-1)**m*(1j)**m*mp.power(3,-mp.mpf(5)/2)*mp.power(27,-mp.mpf(1)/2)
err3=abs(scalar-mp.mpc(0,-1)**m/81)
assert max(err1,err2,err3)<mp.mpf('1e-45'),(m,err1,err2,err3)
a=(mp.mpf(m)+1)/2
R=lambda t:mp.gamma(a+t-mp.mpf(1)/6)*mp.gamma(a+t+mp.mpf(1)/6)/(mp.gamma(a-t-mp.mpf(1)/6)*mp.gamma(a-t+mp.mpf(1)/6))
assert abs(R(mp.mpf('0.27'))*R(mp.mpf('-0.27'))-1)<mp.mpf('1e-55')
out={'status':'PASS','precision':60,'case':args.case,'mode':m,'c':str(c),'ell':str(ell),'bessel_relative_error':mp.nstr(err1,12),'cusp_reflection_relative_error':mp.nstr(err2,12),'scalar_error':mp.nstr(err3,12),'kernel_nearest_numerator_pole':str(-a+mp.mpf(1)/6),'elapsed_seconds':round(time.monotonic()-started,3),'scope':'high-precision single-mode Mellin and reflection; not interval arithmetic or infinite-sum verification'}
t=json.dumps(out,indent=2);r=Path(__file__).parent/'results';r.mkdir(exist_ok=True);(r/('reflection_'+str(args.case)+'.json')).write_text(t);print(t)
