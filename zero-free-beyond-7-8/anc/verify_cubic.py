"""Exact cubic-field identities, interval certificates, root isolation."""
from exact import Q, Field, Interval, DELTA as z, Y as y, endpoint_numerator, general_coefficients, check

def F(u):return 1188*u**3-2160*u**2+171*u+190
def G(s):return 7884*s**3-18819*s**2+14643*s-3686
check('irreducible cubic modulo seven',1188%7==5 and [F(u)%7 for u in range(7)]==[1,5,3,4,3,2,3])
I=Interval(Q(3885833,10**7),Q(3885834,10**7))
check('F lower sign',F(I.lo)==Q(13153091803447489,250000000000000000000)>0)
check('F upper sign',F(I.hi)==-Q(1385634440463739,31250000000000000000)<0)
check('F derivative bound',3564*Q(2,5)**2-4320*Q(19,50)+171==-Q(22509,25)<-900)
K=Field([Q(190,1188),Q(171,1188),-Q(2160,1188),1])
d=K([0,1])
ell=(5-6*d)/(9+18*d)
s=(7+18*d)/(9+18*d)
k=(5+18*d)/(9+18*d)
c=(3+6*d)/(5+18*d)
b=-8*(216*d*d+18*d-13)/(3*(2*d+1)*(792*d*d-618*d-203))
check('cubic field relation',F(d)==0)
check('self consistency',s==Q(11,12)-ell/4 and k==2*s-1 and c==1/(3*k))
check('stationary equation',(4752*d**3-1332*d*d-3072*d-609)*b+1728*d*d+144*d-104==0)
aa,a1,b1,c1,a2,b2,a3=general_coefficients(ell,b,c)
nn=endpoint_numerator(ell,b,c)
rhs=(z-d)**2*aa+y*(z*z*a1+z*b1+c1)+y*y*(z*z*a2+z*b2)+y**3*z*z*a3
check('cubic full numerator and double root',nn==rhs)
check('cubic endpoint equation',G(s)==0)

# Polynomial identities in an independent rational indeterminate.
u=z
num=7+18*u; den=9+18*u
check('elimination polynomial identity',7884*num**3-18819*num*num*den+14643*num*den*den-3686*den**3==108*F(u))
jn=(Q(5,6)-u)*(19+78*u)+u*(7+30*u)
check('general critical rational identity',2*jn*(Q(1,3)-u)+(Q(5,6)-u)*u*(7+30*u)==F(u)/18)
cc=(3+6*d)/(5+18*d)
D=(5-2*cc)/2;P=(2-cc)/2;J=(Q(5,6)-d)*D+d*P
R=1-d+(Q(5,6)-d)*d*P/(2*J)
check('critical count equals two thirds',R==Q(2,3))

# Direct interval evaluation, before reducing by F. No numerical roots.
di=I
li=(5-6*di)/(9+18*di)
si=(7+18*di)/(9+18*di)
ki=(5+18*di)/(9+18*di)
ci=(3+6*di)/(5+18*di)
bi=-8*(216*di*di+18*di-13)/(3*(2*di+1)*(792*di*di-618*di-203))
bd=792*di*di-618*di-203
rd=288*di*di-318*di-95
check('b denominator interval',-324<bd.lo<=bd.hi<-323)
check('critical denominator interval',-176<rd.lo<=rd.hi<-175)
av,a1v,b1v,c1v,a2v,b2v,a3v=general_coefficients(li,bi,ci)
items={
 'ell':(li,Q(1,6),Q(17,100)),
 'b':(bi,Q(1,10),Q(13,100)),
 'kappa':(ki,Q(37,50),Q(3,4)),
 'c':(ci,Q(444495,10**6),Q(444496,10**6)),
 'A0':(av,25,None),'A1':(a1v,65,None),'A2':(a2v,46,None),
 'square1':(4*a1v*(c1v+Q(1,4))-b1v*b1v,3,None),
 'square2':(4*a2v/25-b2v*b2v,3,None),
 'Q1prime(.3)':(Q(3,5)*a1v+b1v,7,None),
 'Q1(.3)':(Q(9,100)*a1v+Q(3,10)*b1v+c1v,-Q(1,100),None),
 'Q1(1/3)':(a1v/9+b1v/3+c1v,Q(3,10),None),
 'Q2(.3)/.3':(Q(3,10)*a2v+b2v,11,None),
}
for label,(v,lo,hi) in items.items():
    check(label,v.lo>lo and (hi is None or v.hi<hi))
    print('DIRECT_INTERVAL',label,v)
    scale=10**6
    lower=Q((v.lo*scale).__floor__(),scale)
    upper=Q((v.hi*scale).__ceil__(),scale)
    print('PRINTABLE_INTERVAL',label,lower,upper)

# The displayed parameter rows may also be used directly, with wider intervals.
lround=Interval(Q(166838,10**6),Q(166839,10**6))
bround=Interval(Q(123405,10**6),Q(123406,10**6))
cround=Interval(Q(444495,10**6),Q(444496,10**6))
a0r,a1r,b1r,c1r,a2r,b2r,a3r=general_coefficients(lround,bround,cround)
rounded_guards=[
    a0r.lo>25, a1r.lo>65, a2r.lo>46,
    (4*a1r*(c1r+Q(1,4))-b1r*b1r).lo>0,
    (4*a2r/25-b2r*b2r).lo>0,
    (Q(3,5)*a1r+b1r).lo>0,
    (Q(9,100)*a1r+Q(3,10)*b1r+c1r).lo>-Q(1,100),
    (a1r/9+b1r/3+c1r).lo>Q(3,10),
    (Q(3,10)*a2r+b2r).lo>0, a3r.lo>0,
]
check('rounded printed parameter rows imply every sign guard',all(rounded_guards))

check('cover1',Q(19,100)-Q(1,4)/2-Q(1,25)/4==Q(11,200)>0)
check('cover2',Q(3,40)-Q(1,100)/2==Q(7,100)>0)
sa,sb=Q(8749570194,10**10),Q(8749570195,10**10)
check('sigma lower sign',G(sa)>0)
check('sigma upper sign',G(sb)<0)
print('G_LOWER',G(sa),'G_UPPER',G(sb))
fine_lo,fine_hi=Q(874957019420098946,10**18),Q(874957019420098947,10**18)
check('fine root isolation',G(fine_lo)>0>G(fine_hi))
print('DECIMAL_ISOLATION',fine_lo,fine_hi)
check('sigma derivative guard',23652*Q(7,8)**2-37638*Q(8749,10000)+14643<-170)
check('rational corollary',sb<Q(43747851,50000000)==Q(7,8)-Q(2149,50000000))
# A sharper square isolation, used only to compare the two endpoints.
from math import isqrt
ri=isqrt(921*10**28)
rl,rh=Q(ri,10**14),Q(ri+1,10**14)
check('sharp sqrt isolation',rl**2<921<rh**2)
print('SHARP_SQRT_INTERVAL',rl,rh)
check('cubic improves quadratic by > 1/20000000',(1507-2*rh)/1653-sb>Q(1,20000000))
print('All cubic-field and interval certificates verified.')
