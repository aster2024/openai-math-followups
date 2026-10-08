"""Exact Q(sqrt(921)) identities and rational sign bounds."""
from exact import Q, Field, Interval, DELTA as d, Y as y, endpoint_numerator, general_coefficients, check

K=Field([-921,0,1])
r=K([0,1])
I=Interval(Q(30347,1000),Q(30348,1000))
check('sqrt lower square gap',921-I.lo**2==Q(59591,10**6)>0)
check('sqrt upper square gap',I.hi**2-921==Q(1104,10**6)>0)
dc=(49-r)/48
ell=(33+8*r)/1653
b=-Q(4,29)+230*r/26709
sigma=(1507-2*r)/1653
check('quadratic critical equation',288*dc**2-588*dc+185==0)
check('quadratic geometry',ell==(5-6*dc)/(9+18*dc) and sigma==Q(11,12)-ell/4)
aa,a1,b1,c1,a2,b2,a3=general_coefficients(ell,b,Q(4,9))
n=endpoint_numerator(ell,b)
rhs=(d-dc)**2*aa+y*(d*d*a1+d*b1+c1)+y*y*(d*d*a2+d*b2)+y**3*d*d*a3
check('quadratic full numerator and double root',n==rhs)
items={
 'A0':(aa,25), 'dstar':(dc,Q(777,2000)),
 'A1':(a1,65), 'A2':(a2,46),
 'square1':(4*a1*(c1+Q(6,25))-b1*b1,1),
 'square2':(4*a2*Q(3,125)-b2*b2,Q(1,30)),
 'Q1prime(.3)':(Q(3,5)*a1+b1,7),
 'Q1(.3)':(Q(9,100)*a1+Q(3,10)*b1+c1,-Q(1,200)),
 'Q1(1/3)':(a1/9+b1/3+c1,Q(3,10)),
 'Q2(.3)/.3':(Q(3,10)*a2+b2,11),
}
for label,(value,lower) in items.items():
    enclosure=value.interval(I)
    check(label,enclosure.lo>lower)
    print('FIELD',label,value,'ENCLOSURE',enclosure)
check('square1 exact expression',items['square1'][0]==(17317418985607-570341476744*r)/6990413025)
check('square2 exact expression',items['square2'][0]==(-6767947591748+223064581728*r)/34952065125)
check('derivative exact expression',items['Q1prime(.3)'][0]==-Q(2729,145)+117028*r/133545)
check('near zero exact expression',items['Q1(.3)'][0]+Q(1,200)==Q(2140057,66120)-40590578*r/38060325)
check('Q1 third exact expression',items['Q1(1/3)'][0]==Q(52541,1653)-1578082*r/1522413)
check('Q2 guard exact expression',items['Q2(.3)/.3'][0]==Q(1956,145)-6736*r/133545)
check('first cover square lower',25*(Q(777,2000)-Q(3,10))**2>Q(19,100))
check('second cover square lower',25*(Q(777,2000)-Q(1,3))**2>Q(3,40))
check('first cover remainder',Q(19,100)-Q(6,25)/2-Q(3,125)/4==Q(8,125)>0)
check('second cover remainder',Q(3,40)-Q(1,200)/2==Q(29,400)>0)
check('ell box',Q(1,6)<ell.interval(I).lo<=ell.interval(I).hi<Q(17,100))
check('b box',Q(1,10)<b.interval(I).lo<=b.interval(I).hi<Q(13,100))
check('second rational gain',(ell-Q(1001,6000)).interval(I).lo==Q(1,3306000))
print('The actual root is strictly above the lower isolating endpoint, hence the last bound is strict.')
print('All quadratic-field certificates verified.')
