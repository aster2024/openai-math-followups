#!/usr/bin/env python3
"""Numerical sanity checks for the paper (not part of the proofs).  Run: python3 checks.py  (< 30 s).

 1. exact integrals K0, J against the closed-form bounds K0+, J+ used in Proposition 4.1;
 2. the partial-sum bound sum_{n<=q} n^{-sigma_0} <= q^{delta'}/delta' at sample q;
 3. the prime-power count bound sum_{k>=2} pi(y^{1/k})/k <= sqrt(y)/2 + y^{1/3} log y at sample y;
 4. Rosser-Schoenfeld (3.6) and the lower bound of their Theorem 7 at sample x;
 5. the Perron kernel identity;
 6. class numbers h(-d), d <= 3*10^6, against Corollary 1.3 (cannot fail, see Section 6; sanity only);
 7. |L(1,chi)| for all nonprincipal characters modulo primes q <= 1500 against Corollary 1.2.
"""
import math, sys, time
import numpy as np
from mpmath import mp, mpf, quad, inf, sqrt, log, asinh, euler, exp, pi, zeta, quad as mpquad, mpc

sys.path.insert(0, '.')
from constants import params, Theta, Clow, Cup, hbound

mp.dps = 20
t0 = time.time()

print("== 1. K0, J: exact integrals vs bounds ==")
for th in [mpf(7) / 8, mpf(1) / 2]:
    P = params(th)
    a, T0 = P['a'], P['T0']
    f = lambda v: 1 / (sqrt(a ** 2 + v ** 2) * sqrt((1 - a) ** 2 + v ** 2))
    K0 = 2 * quad(f, [0, 1, 10, inf])
    J = 2 * quad(lambda v: log(v + T0) * f(v), [0, 1, 10, inf])
    print(f"  theta={float(th):.4f}: K0 = {float(K0):.5f} <= K0+ = {float(P['K0p']):.5f}: {K0 <= P['K0p']};"
          f"  J = {float(J):.5f} <= J+ = {float(P['Jp']):.5f}: {J <= P['Jp']}")

print("== 2. sum_{n<=q} n^-sigma0 <= q^delta'/delta' ==")
for th in [mpf(7) / 8, mpf(1) / 2]:
    P = params(th); s0, dp = float(P['s0']), float(P['dp'])
    ok = True
    for q in [3, 4, 5, 7, 10, 100, 1000, 10 ** 5, 10 ** 6]:
        n = np.arange(1, q + 1, dtype=np.float64)
        lhs = np.sum(n ** (-s0)); rhs = q ** dp / dp
        ok &= lhs <= rhs
    print(f"  theta={float(th):.4f}: all sample q pass: {ok}  (q=10^6: {lhs:.4f} <= {rhs:.4f})")

print("== 3. prime-power count: sum_{k>=2} pi(y^(1/k))/k <= sqrt(y)/2 + y^(1/3) log y ==")
N = 10 ** 7
sieve = np.ones(N + 1, dtype=bool); sieve[:2] = False
for p in range(2, int(N ** 0.5) + 1):
    if sieve[p]:
        sieve[p * p::p] = False
primes = np.nonzero(sieve)[0]
pic = np.cumsum(sieve)  # pi(n)
for y in [10 ** 5, 10 ** 6, 10 ** 7]:
    s = 0.0
    k = 2
    while y ** (1 / k) >= 2:
        s += pic[int(math.floor(y ** (1 / k) + 1e-9))] / k
        k += 1
    rhs = math.sqrt(y) / 2 + y ** (1 / 3) * math.log(y)
    print(f"  y={y}: lhs={s:.3f} <= rhs={rhs:.3f}: {s <= rhs}")

print("== 4. Rosser-Schoenfeld (3.6) and Theorem 7 (lower bound, x >= 285) ==")
x = np.arange(2, N + 1, dtype=np.float64)
r = pic[2:] * np.log(x) / x
print(f"  max_(x<=1e7) pi(x) log x/x = {r.max():.6f} at x = {int(x[np.argmax(r)])}  (< 1.25506: {r.max() < 1.25506})")
logp = np.log(1 - 1 / primes.astype(np.float64))
cum = np.cumsum(logp)
ok = True
for X in [285, 286, 300, 1000, 10 ** 4, 10 ** 5, 10 ** 6, 10 ** 7]:
    prod = math.exp(cum[pic[X] - 1])
    lb = math.exp(-float(euler)) / math.log(X) * (1 - 1 / (2 * math.log(X) ** 2))
    ok &= prod > lb
    print(f"  x={X}: prod(1-1/p) = {prod:.8f} > e^-gamma/log x (1-1/(2log^2 x)) = {lb:.8f}: {prod > lb}")
print(f"  all pass: {ok}")

print("== 5. Perron kernel (1/2 pi i) int_(c) x^w dw/(w(w+1)) = max(0, 1-1/x) ==")
for xx in [mpf('0.5'), mpf(1), mpf(2), mpf(10)]:
    c = mpf(1)
    g = lambda v: (xx ** mpc(c, v)) / (mpc(c, v) * mpc(c + 1, v))
    pts = [-inf] + [-mpf(10) ** k for k in range(6, -1, -1)] + [0] + [mpf(10) ** k for k in range(0, 7)] + [inf]
    val = mpquad(g, pts) / (2 * pi)
    print(f"  x={float(xx)}: integral = {complex(val).real:.8f}  target = {float(max(0, 1 - 1 / xx)):.8f}")

print("== 6. class numbers h(-d) for fundamental d <= 3*10^6 vs Corollary 1.3 ==")
Nd = 3_000_000
h = np.zeros(Nd + 1, dtype=np.int32)
amax = int(math.isqrt(Nd // 3))
for A in range(1, amax + 1):
    step = 4 * A
    for B in range(-A + 1, A + 1):
        cmin = A if B >= 0 else A + 1
        d0 = 4 * A * cmin - B * B
        if d0 > Nd:
            continue
        h[d0::step] += 1
sqf = np.ones(Nd + 1, dtype=bool); sqf[0] = False
for p in range(2, math.isqrt(Nd) + 1):
    sqf[p * p::p * p] = False
dd = np.arange(Nd + 1)
fund = np.zeros(Nd + 1, dtype=bool)
fund[3::4] = sqf[3::4]
m = dd // 4
fund[4::4] = ((m[4::4] % 4 == 1) | (m[4::4] % 4 == 2)) & sqf[m[4::4]]
fund[:3] = False
D = dd[fund].astype(np.float64); H = h[fund].astype(np.float64)
assert h[163] == 1 and h[4027] == 9 and h[1555] == 4
print(f"  #fundamental d in [3, {Nd}]: {fund.sum()}; spot checks h(-163)=1, h(-1555)=4, h(-4027)=9 ok")
for Hmax, known in [(1, 163), (10, 13843), (100, 2383747)]:
    w = dd[fund & (h <= Hmax)]
    print(f"  largest fundamental d <= {Nd} with h(-d) <= {Hmax}: {int(w.max())} (literature value: {known}); h(-{int(w.max())}) = {int(h[w.max()])}")
P = params(mpf(7) / 8)
C_unif = 32.69   # rounded constant of Corollary 1.3 (exact value pi*Clow(3) = 32.6832...)
lb = np.sqrt(D) / (C_unif * (10 + np.log(np.log(D))))
print(f"  bound sqrt(d)/({C_unif}(10+loglog d)): violations = {(H < lb).sum()}, min h/bound = {(H / lb).min():.2f} at d = {int(D[np.argmin(H / lb)])}, max bound in range = {lb.max():.3f}")
# q-dependent bound with the best M of Table 1 for H=1 (M=7): evaluate at a grid of d
viol = 0
for d in [3, 7, 163, 1000, 10 ** 4, 10 ** 5, 299_999]:
    if fund[d]:
        b = float(hbound(P, mpf(7), mpf(d)))
        viol += h[d] < b
print(f"  q-dependent bound (M=7) at sample d: violations = {viol}")

print("== 7. |L(1,chi)| for all nonprincipal chi mod primes q <= 1500 vs Corollary 1.2 ==")
try:
    from scipy.special import digamma
    Cl, Cu = float(Clow(P, 10, 3)), float(Cup(P, 10, 3))
    worst_lo, worst_hi, count = float('inf'), 0.0, 0
    q_lo = None
    for q in primes[primes <= 1500]:
        q = int(q)
        if q < 3:
            continue
        # primitive root
        phi = q - 1
        fac = [f for f in range(2, phi + 1) if phi % f == 0 and all(f % g for g in range(2, int(f ** 0.5) + 1))]
        g = next(gg for gg in range(2, q) if all(pow(gg, phi // f, q) != 1 for f in fac))
        pw = np.empty(phi, dtype=np.int64); v = 1
        for k in range(phi):
            pw[k] = v; v = v * g % q
        psi = digamma(pw / q)                    # psi(g^k / q)
        Lvals = -np.fft.fft(psi) / q             # L(1, chi_j) = -(1/q) sum_k e(jk/phi) psi(g^k/q)  (j = 1..phi-1)
        absL = np.abs(Lvals[1:])
        lo = 1 / (Cl * (10 + math.log(math.log(q)))); hi = Cu * (10 + math.log(math.log(q)))
        if absL.min() / lo < worst_lo:
            worst_lo, q_lo = absL.min() / lo, q
        worst_hi = max(worst_hi, absL.max() / hi); count += phi - 1
    print(f"  {count} characters; min |L|/lower = {worst_lo:.3f} at q = {q_lo} (>= 1 required), max |L|/upper = {worst_hi:.4f} (<= 1 required)")
    # cross-check one value: L(1, chi_{-7}) = pi h(-7)/sqrt(7) with h = 1
    q = 7; pw = np.array([3 ** k % 7 for k in range(6)]); psi = digamma(pw / 7)
    L7 = -np.fft.fft(psi) / 7
    print(f"  check: |L(1,chi_-7)| = {abs(L7[3]):.10f}, pi/sqrt(7) = {math.pi / math.sqrt(7):.10f}")
except ImportError:
    print("  scipy not available; skipped")
print(f"total {time.time() - t0:.1f} s")
