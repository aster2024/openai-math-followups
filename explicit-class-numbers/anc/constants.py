#!/usr/bin/env python3
"""Explicit constants of the paper "Explicit Littlewood-type bounds for L(1,chi) and class
numbers from a zero-free half-plane" (Theorem 1.1, Corollaries 1.2-1.3, Table 1).

Every quantity is defined exactly as in the paper; see Section 2 (constants) and Section 5.
Run:  python3 constants.py            (mpmath, ~2 s)
"""
from mpmath import mp, mpf, log, exp, sqrt, asinh, pi, zeta, euler, quad, inf, findroot, ceil

mp.dps = 30
G2 = zeta(2)
RS36 = mpf('1.25506')          # Rosser-Schoenfeld (3.6): pi(x) < 1.25506 x/log x, x > 1
LOGLOG3 = log(log(3))


def params(theta):
    """Geometric parameters of Section 2 as functions of theta (1/2 <= theta < 1)."""
    theta = mpf(theta)
    delta = 1 - theta
    a = 22 * delta / 25            # inner disc reaches Re s = 1 - a
    dp = 24 * delta / 25           # outer disc reaches Re s = 1 - dp  (delta' in the paper)
    R, r = 1 + dp, 1 + a
    s0 = 1 - dp                    # sigma_0
    kappa = 2 * r / (R - r)        # Borel-Caratheodory factor = 25/delta + 22
    T0 = 2 + 2 * R + s0 / dp
    A1 = kappa * dp
    A2 = kappa
    A3 = kappa * log(1 / s0) + (kappa + 1) * log(G2)
    K0p = 2 * asinh(1 / a) / (1 - a) + 2
    Jp = 2 * log(1 + T0) * (asinh(1 / a) / (1 - a) + 1 + 1 / T0)
    return dict(theta=theta, delta=delta, a=a, dp=dp, R=R, r=r, s0=s0, kappa=kappa, T0=T0,
                A1=A1, A2=A2, A3=A3, K0p=K0p, Jp=Jp)


def E0(P, M, q):
    """Bound for the Perron remainder |E| (Proposition 4.1) at modulus q."""
    return (P['A1'] * P['K0p'] + (P['A2'] * P['Jp'] + P['A3'] * P['K0p']) / log(q)) / (2 * pi * exp(M))


def Theta(P, M, q):
    """Theta(q) of Theorem 1.1: total error in the exponent."""
    L = (M + log(log(q))) / P['a']        # log y
    y = exp(L)
    return (E0(P, M, q) + RS36 / L + mpf('2.5') / sqrt(y) + L / y ** (mpf(2) / 3)
            + 1 / (2 * L ** 2 - 1) + 2 / y)


def Clow(P, M, q):
    return exp(euler) / (P['a'] * G2) * exp(Theta(P, M, q))


def Cup(P, M, q):
    return exp(euler) / P['a'] * exp(Theta(P, M, q))


def hbound(P, M, d, uniform=False):
    """Lower bound for h(-d) from Corollary 1.3: sqrt(d)/(pi*Clow*(M+loglog d))."""
    C = Clow(P, M, 3) if uniform else Clow(P, M, d)
    return sqrt(d) / (pi * C * (M + log(log(d))))


def threshold(P, M, H, uniform=False):
    """Least real d0 with hbound(d) >= H for all d >= d0 (hbound is increasing in d)."""
    f = lambda x: hbound(P, M, exp(x), uniform) - H
    # bracket in log d
    lo, hi = mpf(2), mpf(2)
    while f(hi) < 0:
        hi += 5
    x = findroot(f, (lo, hi), solver='bisect', tol=mpf(10) ** -20)
    return exp(x)


def report(theta, M, label):
    P = params(theta)
    print(f"\n==== theta = {label} = {float(P['theta']):.10f},  M = {M} ====")
    for k in ['delta', 'a', 'dp', 'R', 'r', 's0', 'kappa', 'T0', 'A1', 'A2', 'A3', 'K0p', 'Jp']:
        print(f"  {k:6s} = {P[k]}")
    for q in [3, 10 ** 9]:
        L = (M + log(log(q))) / P['a']
        print(f"  q = {q}: log y = {float(L):.4f}, E0 = {float(E0(P, M, q)):.6f}, "
              f"1.25506/log y = {float(RS36 / L):.6f}, Theta = {float(Theta(P, M, q)):.6f}, "
              f"Clow = {float(Clow(P, M, q)):.4f}, Cup = {float(Cup(P, M, q)):.4f}, "
              f"pi*Clow = {float(pi * Clow(P, M, q)):.4f}")
    return P


if __name__ == '__main__':
    print("Fixed numerical inputs:")
    print(f"  zeta(2) = {G2},  log zeta(2) = {log(G2)},  e^gamma = {exp(euler)},  e^gamma/zeta(2) = {exp(euler) / G2}")
    print(f"  2*pi*e^10 = {2 * pi * exp(10)}")
    print(f"  Lemma A (Theorem 1.4): e^(31/40) = {exp(mpf(31) / 40)} < 2.171; 2.171*31 = {mpf('2.171') * 31} < 68;"
          f" 30 log(3/4) = {30 * log(mpf(3) / 4)}; 400*3^(1/2+30 log(3/4)) = {400 * mpf(3) ** (mpf(1) / 2 + 30 * log(mpf(3) / 4))} < 0.06")

    sigma_dagger = findroot(lambda s: 7884 * s ** 3 - 18819 * s ** 2 + 14643 * s - 3686, mpf('0.874957'))
    thetas = [(mpf(7) / 8, '7/8'), (sigma_dagger, 'sigma_dagger'), (mpf('0.8739558'), 'tracker 4369779/5000000'),
              (mpf(1) / 2, '1/2 (GRH)')]
    M0 = 10
    Ps = {}
    for th, lab in thetas:
        Ps[lab] = report(th, M0, lab)

    # ---- headline constants for theta = 7/8, M = 10 (Corollary 1.2) ----
    P = Ps['7/8']
    print("\n==== Corollary 1.2 (theta = 7/8, M = 10), uniform in q >= 3 ====")
    print(f"  Theta(3) = {Theta(P, M0, 3)}")
    print(f"  Clow(3)  = {Clow(P, M0, 3)}   -> |L(1,chi)| >= 1/(Clow (10 + loglog q))")
    print(f"  Cup(3)   = {Cup(P, M0, 3)}    -> |L(1,chi)| <= Cup (10 + loglog q)")
    print(f"  pi*Clow(3) = {pi * Clow(P, M0, 3)}   -> h(-d) >= sqrt(d)/(pi*Clow (10 + loglog d))")
    print(f"  bound (i): A1 = {P['A1']}, A2 = {P['A2']}, A3 = {P['A3']}, T0 = {P['T0']}")

    # ---- Table: thresholds d0(H) ----
    print("\n==== Table 1: thresholds d0(H): h(-d) > H for all d >= d0 (theta = 7/8) ====")
    Hs = [1, 10, 100, 1000, 2000, 10 ** 5]
    Ms = [mpf(5) + mpf(k) / 4 for k in range(0, 41)]   # M = 5, 5.25, ..., 15
    for H in Hs:
        d_unif = threshold(P, M0, H, uniform=True)
        best = None
        for M in Ms:
            d = threshold(P, M, H, uniform=False)
            if best is None or d < best[1]:
                best = (M, d)
        print(f"  H = {H:>6d}: uniform M=10: d0 = {float(d_unif):.4e};  q-dependent, best M = {float(best[0]):.2f}: d0 = {float(best[1]):.4e}")

    # ---- same for the tracker value and sigma_dagger, H = 100 ----
    print("\n==== thresholds for H = 100 at other theta (uniform M = 10 / best M) ====")
    for lab in ['sigma_dagger', 'tracker 4369779/5000000', '1/2 (GRH)']:
        Pt = Ps[lab]
        d_unif = threshold(Pt, M0, 100, uniform=True)
        best = min(((M, threshold(Pt, M, 100, uniform=False)) for M in Ms), key=lambda t: t[1])
        print(f"  theta = {lab}: d0(100) uniform = {float(d_unif):.4e}; best M = {float(best[0]):.2f}: {float(best[1]):.4e}")

    # ---- thresholds with the ROUNDED constant 32.69 of Corollary 1.3 (used in the text) ----
    print("\n==== thresholds with the rounded constant 32.69 (Corollary 1.3 as stated) ====")
    CR = mpf('32.69')
    for H in Hs + [101]:
        g = lambda x: sqrt(exp(x)) - CR * H * (M0 + log(x))
        x0 = findroot(g, (mpf(2), mpf(60)), solver='bisect', tol=mpf(10) ** -20)
        print(f"  H = {H:>6d}: d0 = {float(exp(x0)):.5e}   (sqrt(d) = 32.69 H (10 + loglog d))")
    g = lambda x: sqrt(exp(x)) - CR * 2 * (M0 + log(x))
    print(f"  bound < 2 for d < {float(exp(findroot(g, (mpf(2), mpf(60)), solver='bisect', tol=mpf(10)**-20))):.5e}")
    for ld in [mpf('27.2'), mpf('35.4')]:
        d = exp(ld)
        print(f"  at d = e^{float(ld)}: sqrt(d)/(32.69 (10 + loglog d)) = {float(sqrt(d) / (CR * (M0 + log(ld)))):.1f}")

    # ---- where the Littlewood-type bound beats the Hecke-Landau-type bound 1/(120 log q) ----
    f = lambda x: 120 * x - Clow(P, M0, 3) * (M0 + log(x))
    x0 = findroot(f, 2)
    print(f"\n  1/(Clow(10+loglog q)) > 1/(120 log q)  iff  log q > {x0} (q > {exp(x0)})")
    # upper bound 17.12(10+loglog q) vs trivial log q + 2
    f2 = lambda x: (x + 2) - mpf('17.12') * (M0 + log(x))
    x2 = findroot(f2, 250)
    print(f"  17.12(10+loglog q) < log q + 2  iff  log q > {x2}")
    # lower bound vs Mossinghoff-Starichkova-Trudgian 1/(9.69030 log(q/pi)) (complex chi)
    f3 = lambda x: mpf('9.69030') * (x - log(pi)) - mpf('10.41') * (M0 + log(x))
    x3 = findroot(f3, 15)
    print(f"  1/(10.41(10+loglog q)) > 1/(9.69030 log(q/pi))  iff  log q > {x3} (q > {float(exp(x3)):.3e})")
    print(f"  Theorem 1.4 range: 1 - 1/(40 log 3) = {1 - 1 / (40 * log(3))}")
    L3 = (M0 + LOGLOG3) / P['a']
    print(f"  small terms of Theta(3): 1/(2L^2-1) = {1 / (2 * L3 ** 2 - 1)}, 2.5/sqrt(y) = {mpf('2.5') * exp(-L3 / 2)}, L/y^(2/3) = {L3 * exp(-2 * L3 / 3)}, 2/y = {2 * exp(-L3)}")

    # ---- Kimura's comparison numbers (arXiv:2610.21511v2, Table 1 / Remark 11), for the text ----
    print("\n==== comparison values from Kimura (quoted, not computed here) ====")
    print("  unconditional thresholds e^{T_N}: N=100: 2.8510e12, 200: 1.2364e13, 500: 7.9422e13, 1000: 3.4539e14, 2000: 1.6069e15")
    print("  conditional on a half-plane Re s > 31/32 (Remark 11): h > 2000 for log d >= 27.2 (d >= e^27.2 = %.3e); h > 1e5 for log d >= 35.4 (%.3e)"
          % (float(exp(mpf('27.2'))), float(exp(mpf('35.4')))))
    for H, ld in [(2000, mpf('27.2')), (10 ** 5, mpf('35.4'))]:
        d = exp(ld)
        print(f"  our bound at d = e^{float(ld)}: uniform M=10: h >= {float(hbound(P, M0, d, True)):.1f}; q-dependent M=10: {float(hbound(P, M0, d)):.1f}; "
              f"best over M: {float(max(hbound(P, M, d) for M in Ms)):.1f}  (target {H})")
