"""Exact symbolic identities for the geometry and finite-transform ledgers.

Uses a sparse polynomial ring over Fraction, without a CAS or numerical sampling.
Inequality hypotheses are proved in the manuscript, not inferred from samples.
"""
from fractions import Fraction as Q
from exact import check, Interval


class P:
    def __init__(self, terms=None):
        self.t = {k:v for k,v in (terms or {}).items() if v}

    @staticmethod
    def cast(x):
        return x if isinstance(x,P) else P({():Q(x)})

    def __add__(self,b):
        out=self.t.copy()
        for k,v in self.cast(b).t.items():out[k]=out.get(k,0)+v
        return P(out)

    __radd__=__add__

    def __neg__(self):return P({k:-v for k,v in self.t.items()})
    def __sub__(self,b):return self+-self.cast(b)
    def __rsub__(self,b):return self.cast(b)+-self

    def __mul__(self,b):
        out={}
        for k,v in self.t.items():
            for j,w in self.cast(b).t.items():
                a=tuple(sorted(k+j))
                out[a]=out.get(a,0)+v*w
        return P(out)

    __rmul__=__mul__
    def __truediv__(self,b):return P({k:v/Q(b) for k,v in self.t.items()})
    def __pow__(self,n):
        out=P.cast(1)
        for _ in range(n):out*=self
        return out
    def __eq__(self,b):return self.t==self.cast(b).t
    def at(self,**values):
        out=Q(0)
        for names,coefficient in self.t.items():
            term=coefficient
            for name in names:term*=values[name]
            out+=term
        return out


def symbols(names):
    return [P({(s,):Q(1)}) for s in names.split()]


# Coefficient formulas printed before the endpoint stages; independent symbolic
# expansion in all five indeterminates, including the constant coefficient.
el,be,ce,de,ye=symbols("el be ce de ye")
xx=Q(1,2)-ye
Ax=2-2*ce*xx
Bx=1-xx
Dx=Ax+Bx
Px=Ax*Bx
Jx=(Q(5,6)-de)*Dx+de*Px
hh=(1+be+3*el)/2
e0=-Q(1,4)+be/6+5*el/4
numer=-108*Jx*(e0-(be/2+el*ye)*de)-54*hh*(Q(5,6)-de)*de*Px
A0x=27*be*ce/2-54*be-81*ce*el/2-27*ce/2+81*el+27
B0x=-54*(ce-3)*e0+45*be*(5-2*ce)/2-45*hh*(2-ce)/2
C0x=-45*(5-2*ce)*e0
A1x=-108*be*ce+108*be+54*ce*el+54
B1x=126*be*ce-18*be+180*ce*el-54*ce-45*el-18
C1x=-30*be*ce-15*be-225*ce*el+45*ce-225*el/2+Q(45,2)
A2x=162*be*ce-54*ce*el+54*ce+108*el
B2x=-81*be*ce-225*ce*el+9*ce+90*el
check('general endpoint coefficients including B0 and C0',
      numer==A0x*de**2+B0x*de+C0x+ye*(A1x*de**2+B1x*de+C1x)
            +ye**2*(A2x*de**2+B2x*de)+216*ce*el*ye**3*de**2)
uu=symbols("uu")[0]
jnum=(Q(5,6)-uu)*(19+78*uu)+uu*(7+30*uu)
check('J numerator explicit polynomial',jnum==-(288*uu**2-318*uu-95)/6)
# Clear the denominator 2(5+18u) in the definition of J.
check('J numerator from row definitions',
      (Q(5,6)-uu)*(5*(5+18*uu)-2*(3+6*uu))+uu*(2*(5+18*uu)-(3+6*uu))==jnum)
check('critical count numerator',
      2*jnum*(Q(1,3)-uu)+(Q(5,6)-uu)*uu*(7+30*uu)
      ==(1188*uu**3-2160*uu**2+171*uu+190)/18)
lc,cc=9+18*uu,5+18*uu
ln,cn=5-6*uu,3+6*uu
e0n=-lc/4+be*lc/6+5*ln/4
A0n=27*be*cn*lc/2-54*be*lc*cc-81*cn*ln/2-27*cn*lc/2+81*ln*cc+27*lc*cc
B0n=-54*(cn-3*cc)*e0n+45*be*(5*cc-2*cn)*lc/2-45*(lc*(1+be)+3*ln)*(2*cc-cn)/4
stationary=(4752*uu**3-1332*uu**2-3072*uu-609)*be+1728*uu**2+144*uu-104
check('stationary derivative factor without cubic reduction',
      stationary==-(Q(4,27))*(2*uu*A0n+B0n))
check('selected slope lower and upper',Q(33,50)-Q(3,4)/2==Q(57,200)>0
      and 1+Q(5,12)-Q(17,50)==Q(323,300)<2)
check('actual selected slope upper',Q(323,300)+Q(1,4800)<2)
check('floor affine majorant and slope',Q(76,75)-Q(2,3)*Q(1,50)==1
      and Q(101,150)-Q(3,4)/6>0)
check('small-row exponent calculation',Q(17,50)-Q(1,6)==Q(13,75)
      and Q(3,5)+1-Q(17,50)==Q(63,50)<2)
check('fractional slot reserve',Q(1,5)-Q(1,185)==Q(36,185)>Q(7,37)==Q(35,185))

ell,b,delta,x,T,dr,z,R=symbols("ell b delta x T dr z R")
lx,ly,h=(1-b-ell)/2,(1+b-ell)/2,(1+b+3*ell)/2
sg=Q(11,12)-ell/4
cg=lambda s:s-Q(2,3)-b/6
a=(1+delta)/2
amp=x*delta
raw=lx/2+a-1+(1-lx)*z-a*ly+ell*(z-Q(1,2))+amp*ell+dr*(R+delta/2-z)
ed=a-sg+h*(z-Q(1,6))-a*ly-ell/2+amp*ell+dr*(R+delta/2-z)
check('complete retained exponent from raw outside factor',raw-cg(sg)==ed)
check('signal geometry',cg(sg)==lx/2+b/12)
endpoint=-Q(1,4)+b/6+5*ell/4-b*delta/2-ell*(Q(1,2)-x)*delta+h*T
edh=a-sg+h*(z-Q(1,6))-a*ly-ell/2+amp*ell+h*(1-delta+T+delta/2-z)
check('endpoint at d=h',edh==endpoint)
eta,yy=symbols("eta yy")
eh=lambda l:-Q(1,4)+b/6+5*l/4-b*delta/2-l*yy*delta+(1+b+3*l)*T/2
check('first-stage exact increment',eh(Q(1,6)+eta)-eh(Q(1,6))==eta*(Q(5,4)-yy*delta+3*T/2))

# Source completed normalization, at arbitrary new lengths.
mp,O,H,A0,N0,S0,B0,za,lp,theta=symbols("mp O H A0 N0 S0 B0 za lp theta")
DH=mp-O-H
td=2*H+2*A0+2*za-1-lp-theta-N0-3*B0
left=O/2+DH+S0+B0+td/4
right=(2*mp+2*za-1-lp+2*DH-theta)/4+(2*A0-N0+B0+4*S0)/4
check('completed normalization identity',left==right)
dj=symbols("dj")[0]
check('new completed penalty',(1+3*(ell-dj)-2*(1-ell-2*dj))==5*ell+dj-1)

# First finite transform ledger.
mm,qu,c,d,p,rr,ee,ss,Bc,Bd=symbols("mm qu c d p rr ee ss Bc Bd")
AA=symbols("AA")[0]
qtilde=qu+rr+ee
first=(mm-AA-rr/2-ee)+(p+ss)+(AA-c+qtilde+Bc-ss+AA-d+qtilde+Bd-ss)/2
check('first transform total ledger',first==mm+qu+(Bc+Bd-c-d+2*p+rr)/2)

# Second transform and the complete child allowance.
K,g,g2,t2,wo,w,L,b2,p2,V=symbols("K g g2 t2 wo w L b2 p2 V")
M=mm+qu
K0=2*AA-c-d+rr+ee-mm
a0=AA-c-w
J0=d-c+(K0-K)-2*w+wo
mchild=2*a0-K-g-g2-V
qchild=qtilde+wo+t2+V
mc=M+J0-g-g2+t2
check('second transform child width',mchild+qchild==mc)
outside=K+g-L-a0+p2-ss+g2-t2-b2
allowance=a0+qtilde+wo+w+Bc-ss
check('second transform child allowance',allowance-outside==mc+b2-p2+w+Bc+L)
forcing=symbols("forcing")[0]
f1=c/6+5*(d+K0-K)/6+w/3+qtilde/6+wo+Bc-5*g/6+L
f2=2*b2-5*g2/6-p2+t2+V/6+forcing/6
check('exceptional normalization identity',
      (mchild-forcing)/6+a0-b2-(mc+b2-p2+w+Bc+L)==AA-5*M/6-f1-f2)

# General crossing; clear the positive denominator D.
cc,t,r=symbols("cc t r")
Ax=2-2*cc*x;Bx=1-x;Dx=Ax+Bx;Px=Ax*Bx
rn=Ax*t+(cc-1)*x
invD=Dx-delta*(x*Dx+Bx*rn)
plainD=Dx-delta*(cc*x*Dx+Ax*(t*Dx-rn))
shortD=(1-delta)*Dx+delta*Px*(Q(3,2)-t)
check('crossing equality inverse/plain',invD==plainD)
check('weighted crossing value',invD==shortD)
check('crossing polynomial identity',x*(Ax+cc*Bx)==Dx-3*Px/2)

# Model-limit certificates, without optimization or sampling.
u=symbols("u")[0]
Dc=(5-2*cc)/2;Pc=(2-cc)/2
jc=(Q(5,6)-u)*Dc+u*Pc
num=2*jc*(Q(1,3)-u)+(Q(5,6)-u)*u*Pc
den12=6*cc*u-10*cc-18*u+25
jc_c=-Q(5,6)+u/2
check('model derivative in c',
      (Q(5,6)-u)*u*(-jc/2-Pc*jc_c)*den12**2
      ==-u*(6*u-5)**2*jc**2)
vv=symbols("vv")[0]
qqden=Q(5,6)-u+u*vv
check('model derivative of q(u)',
      -vv*qqden-vv*(Q(5,6)-u)*(-1+vv)==-Q(5,6)*vv**2)
u1,u2=Q(19,50),Q(2,5)
N1=(2*((Q(5,6)-u1)*Dc+u1*Pc)*(Q(1,3)-u1)+(Q(5,6)-u1)*u1*Pc)
J1=2*((Q(5,6)-u1)*Dc+u1*Pc)
check('model left endpoint identity',N1*(150*(193*cc-454))==(587*cc-698)*J1)
N2=(2*((Q(5,6)-u2)*Dc+u2*Pc)*(Q(1,3)-u2)+(Q(5,6)-u2)*u2*Pc)
J2=2*((Q(5,6)-u2)*Dc+u2*Pc)
check('model right endpoint identity',N2*(15*(38*cc-89))==(cc+11)*J2)
Ic=Interval(Q(4,9),Q(5000,11247))
check('model endpoint signs',587*Ic.hi-698<0 and 193*Ic.hi-454<0 and 38*Ic.hi-89<0 and Ic.lo+11>0)

print('All symbolic geometry and normalization certificates verified.')
