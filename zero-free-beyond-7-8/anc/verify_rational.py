"""Verify all rational identities printed in the manuscript."""
from exact import Q, DELTA as d, Y as y, endpoint_numerator, check

ell0, b = Q(1,6), Q(1,8)
n0 = endpoint_numerator(ell0,b)
j = (185+170*y+(-138+12*y+96*y*y)*d)/108
v = 51+41*y
rhs = (3+5*y)*((4*v*d-79)**2+49) + 4*y*(4*v*d*((1+3*y)*(15+32*y)*d+9-13*y)+265+3485*y)
check('old endpoint polynomial completion, 10368 v J (-E)',96*v*n0 == rhs)
check('old positive remainder guard',9-13*Q(1,2) == Q(5,2))
check('old denominator majorant',Q(35,54)>0 and Q(5,2)>0)
eta = Q(1,100000)
check('first rational boundary',Q(11,12)-(ell0+eta)/4 == Q(349999,400000))
lx0=Q(17,48)-eta/2
ly0=Q(23,48)-eta/2
h0=Q(13,16)+3*eta/2
check('first geometry lx margin',lx0-(ell0+eta)==Q(37497,200000)>0)
check('first geometry additive margin',ly0-(ell0+eta)-11*b/6==Q(49991,600000)>0)
check('first geometry effective width',1-3*(ell0+eta)==Q(49997,100000)>0)
check('first geometry supply margin',5*(ell0+eta)-h0==Q(12521,600000)>0)
check('first endpoint margin',-Q(49,440640)+15*eta/8 == -Q(20369,220320000))
check('first endpoint strict bound',-Q(20369,220320000) < -Q(9,100000))

ell = Q(1001,6000)
q0 = 612252*d*d-473520*d+91575
q1 = 1572096*d*d-753860*d+84150
q2 = 1128336*d*d-52040*d
q3 = 384384*d*d
check('second rational full numerator',24000*endpoint_numerator(ell,b) == q0+y*q1+y*y*q2+y**3*q3)
check('second rational boundary',Q(11,12)-ell/4 == Q(20999,24000))
check('Q0 discriminant',473520**2-4*612252*91575 == -46717200)
check('Q0 minimum',Q(91575)-Q(473520**2,4*612252) == Q(324425,17007)>19)
check('Q1 completed-square remainder',4*1572096*(84150+6500)-753860**2 == 1737110000)
check('Q2 completed-square remainder',4*1128336*1000-52040**2 == 1805182400)
check('first cover bound',q0.evaluate(Q(3,10),0)-3500 == Q(28042,25)>19)
check('second cover bound',q0.evaluate(Q(1,3),0)+q1.evaluate(Q(3,10),0)/2 == Q(37583,25)>19)
check('shift Q1',q1.evaluate(Q(1,3),0) == Q(22622,3))
check('shift Q2',q2.evaluate(Q(1,3),0) == 108024)
check('rational endpoint bound',Q(19,6480000)>Q(1,350000))

# Geometry bounds: affine functions attain extrema at the four corners.
corners = [(l,b) for l in [Q(1,6),Q(17,100)] for b in [Q(1,10),Q(13,100)]]
for l,b in corners:
    lx,ly,h=(1-b-l)/2,(1+b-l)/2,(1+b+3*l)/2
    check(f'geometry {l},{b}',lx-l>=Q(9,50) and ly-l-11*b/6>=Q(43,600) and 1-3*l>=Q(49,100) and Q(4,5)<=h<=Q(41,50) and 5*l-h>=Q(11,600))
    check(f'floor {l},{b}',-Q(6,25)+Q(32,25)*l+b/6<=-Q(11,15000))
    mid=-Q(2,25)-Q(49,300)*(1+b)+Q(13,50)*l+Q(3,4)*(Q(1,6)-b/4+3*l/4)
    check(f'middle {l},{b}',mid<=-Q(1631,120000))
check('small rows',Q(41,50)*Q(13,75)-Q(93,400)+Q(1,50)==-Q(2111,30000))
check('lattice count elementary bound',Q(8)+Q(1)+Q(6)<16)  # 4 sqrt(2) < 6
check('Euler tail rational guard',Q(210*181,27)<1408 and Q(1408,2**16)<Q(1,32))
check('Euler principal local guard',1400**100 < 2**1740)
check('extended capacity strict guard',9*Q(37,50)**2>4)
check('bootstrap gap fraction',1-Q(41,50)/4==Q(159,200))
check('fourth moment terminal width',Q(25,111)<Q(1,4) and Q(25,516)<Q(1,20))
check('fourth moment terminal reserve',Q(1,100)+Q(1,10**6)+Q(1,600)+Q(3,1000)+Q(1,600)<Q(1,4))

# The conditional certificate verifies algebra only, never its hypothesis.
q0=526080*d*d-406288*d+79365
q1=1292640*d*d-603308*d+72930
q2=920640*d*d-19144*d
q3=322560*d*d
nn=endpoint_numerator(Q(21,125),Q(11,100),alpha=Q(33,40),long_beta=Q(97,120))
check('conditional full numerator',20000*nn==q0+y*q1+y*y*q2+y**3*q3)
check('conditional square Q0',4*526080*(79365-900)-406288**2==45529856)
check('conditional square Q1',4*1292640*72930-603308**2==13108397936)
check('conditional square Q2',4*920640*100-19144**2==1763264)
check('conditional endpoint bound',Q(875)/(20000*108*Q(99,40))==Q(7,42768))
print('All rational certificates verified; no mean-value hypothesis was checked.')
