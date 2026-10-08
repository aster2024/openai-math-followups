"""Exact local identities in Q(i); non-real target phases catch a missing bar."""
from exact import Q, Field, check

K=Field([1,0,1])
i=K([0,1])
for target in [K(1),K(-1),i,-i]:
    for Qp in [7,13]:
        s,w,z=3,3,2
        D=target*Q(1,Qp**s)
        W=Q(1,Qp**w)
        V=Q(1,Qp**(6*z))
        ap=target**3
        R=ap**2*Q(1,Qp**(6*s+6*z-4))
        E=(R*((1-Q(1,Qp))/(1-V)+W-D)
           -target*(Qp-1)*Q(1,Qp**(s+w))*V/(1-V))/(1-R)
        Pstar=-D+E
        PP=(1-V*W)/((1-V)*(1-W))+Pstar
        H=(1-V*W+(1-V)*(1-W)*Pstar)/(1-D)
        tb=target.inverse()
        G=((tb*Qp**s-W)*(1-V)*(1-W)*Pstar-W*(1-V*W))/(1-D)
        # Never introduce floating-point negative powers.
        lhs=tb*Q(Qp**(s+z-1))*Pstar-Q(1,Qp**(w+1-z))*PP
        rhs=(1-D)/((1-V)*(1-W))*Qp**(z-1)*G
        check(f'physical replacement {target},Q={Qp}',lhs==rhs)
        bracket=(1-W)*(V/(1-V)-D)+tb*Qp**s*E+(1-W)*E
        check(f'principal cancellation {target},Q={Qp}',
              G/H+1==(1-V)*(1-W)/((1-D)*H)*bracket)
        if target in [i,-i]:
            wrong=target*Qp**(s+z-1)*Pstar-Q(1,Qp**(w+1-z))*PP
            check(f'missing conjugation rejected {target},Q={Qp}',wrong!=rhs)

# All six table cases, including the exponent on V in the September 30 input paper, (7.11).
for Qp in [7,13]:
    L=Field([-Qp,0,1])
    sqrtQ=L([0,1])
    qp=lambda n: Q(Qp**n) if n>=0 else Q(1,Qp**(-n))
    s,w,z=3,3,2
    V=qp(-6*z)
    for target in [L(1),L(-1)]:
        ap,bp=target**3,target**2
        R=ap**2*qp(4-6*s-6*z)
        for j in range(6):
            rho=L(1)
            D=target*qp(-s) if j==0 else L(0)
            W=qp(-w) if j==0 else Q(0)
            J=[
                -target*qp(-s)+qp(-w)*R,
                target*qp(-s-w),
                ap*sqrtQ**3*qp(-3*s),
                -target*bp*qp(2-3*s-w)+bp**2*qp(2-4*s),
                -target*ap*sqrtQ**5*qp(-4*s-w),
                -ap**2*qp(3-6*s),
            ][j]
            strict=-target*(Qp-1)*qp(-s-w)*V**int(j<=1)
            Pstar=(R*(1-qp(-1))/(1-V)+strict/(1-V)+J)/(1-R)
            PP=(1-V*W)/((1-V)*(1-W))+Pstar
            H=(1-V*W+(1-V)*(1-W)*Pstar)/(1-D)
            G=((target.inverse()*qp(s)-qp(-w))*(1-V)*(1-W)*Pstar
               -qp(-w)*(1-V*W))/(1-D)
            lhs=target.inverse()*qp(s+z-1)*Pstar-qp(z-w-1)*PP
            rhs=(1-D)/((1-V)*(1-W))*qp(z-1)*G
            check(f'six-case replacement Q={Qp},eta={target},j={j}',lhs==rhs)
            if j>=2:
                without=(R*(1-qp(-1))/(1-V)+J)/(1-R)
                check(f'strict ramified term retained Q={Qp},eta={target},j={j}',
                      Pstar-without==strict/((1-V)*(1-R)) and Pstar!=without)

# Entire-column divisor split: the shared-prime zeros are essential.
for n_support in [set(),{2},{3},{2,3},{2,5}]:
    for a_support in [set(),{2},{2,3}]:
        # For a squarefree column n, exactly one d gives (n/d,a)=1.
        eligible=[]
        primes=sorted(a_support)
        for mask in range(1<<len(primes)):
            ds={p for k,p in enumerate(primes) if mask>>k&1}
            if ds<=n_support and not (n_support-ds)&a_support:
                eligible.append(ds)
        check(f'amplifier unique split n={sorted(n_support)},a={sorted(a_support)}',
              eligible==[n_support&a_support])
print('Exact phase and zero-preserving divisor checks passed.')
