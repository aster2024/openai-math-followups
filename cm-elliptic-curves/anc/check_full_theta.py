"""Complete mode-m reflection identity at level one (mask A = 1 mod 3).

LHS  T_m(X) = sum_{n sf, b primary} gtilde(n) alpha(n b^3)^{-m} / (sqrt N(n) N(b)) V(N(n b^3)/X)
RHS  (-i)^m/81 * (1/3) * sum_{cusp j} w_j sum_ell D_j(ell) alpha(ell)^m / sqrt N(ell) * Vsharp_m(N(ell) X)

with V(y)=exp(-(log y)^2/(2 sigma^2)),
     Vsharp_m(x) = (1/2 pi i) int_(0) Vhat(-t) R_m(t) (K x)^{-t} dt,  K=(2 pi)^4/27,
     R_m(t)= prod_{+-} Gamma((m+1)/2 + t +- 1/6)/Gamma((m+1)/2 - t +- 1/6)        [gamma quotient of Section 4]
D_1 = conj tau(-ell)          (theta at cusp 0, i.e. theta itself),   weight 1
D_3 = conj d_10(-ell)         (translate by -omega  -> gamma_10),     weight omega^2
D_2 = conj d_19(-ell)         (translate by +omega  -> gamma_19),     weight omega
tau, tau_1, tau_2 from Dunn-Radziwill (5.7),(5.13),(5.14) (read from the PDF page images, with the bars).
The identity is tested for the claimed kernel index m and, as a control, with a wrong kernel index.
"""
import sys, math, cmath, time, os, signal, json
from pathlib import Path
os.environ["OPENBLAS_NUM_THREADS"]="1"
os.environ["OMP_NUM_THREADS"]="1"
signal.alarm(28)
import numpy as np
from scipy.special import loggamma
from eisenstein_float import *

t0 = time.time()
sigma = 0.6
CUT = 6.5
Xs = [float(x) for x in sys.argv[1].split(',')] if len(sys.argv)>1 else [20.0]
MS = [1, 2, 3, 4]
K = (2 * math.pi) ** 4 / 27
Xmin, Xmax = min(Xs), max(Xs)
# Enlarged dual cutoff. The old heuristic sqrt(N X)<=17 did not reach 1e-8 accuracy.
NELL_MAX = 40.0 ** 2 / Xmin
NA_DUAL = 81 * NELL_MAX
NA_SRC = Xmax * math.exp(CUT * sigma)
NMAX = int(max(NA_DUAL, NA_SRC)) + 1
els, fact, plist = build(NMAX)
print("NMAX", NMAX, "elements", len(els), "primes", len(plist), "t", round(time.time() - t0, 1), flush=True)


def gt(n):
    fs = fact[n]
    z = 1 + 0j
    for P in fs:
        z *= P.gtilde()
    for i in range(len(fs)):
        for k in range(i + 1, len(fs)):
            z *= OM ** ((fs[k].cubic_index(fs[i].pi) + fs[i].cubic_index(fs[k].pi)) % 3)
    return z


def cub(x, n):
    """(x/n)_3 for squarefree primary n, x coprime to n"""
    k = 0
    for P in fact[n]:
        k += P.cubic_index(x)
    return OM ** (k % 3)


sf = [n for n in els if len(set(P.pi for P in fact[n])) == len(fact[n])]
gval = {n: gt(n) for n in sf}
LAM2 = mul((1, 2), (1, 2))            # lambda^2 = -3
OML2 = mul((0, 1), LAM2)              # omega lambda^2
OM2L2 = mul((-1, -1), LAM2)           # omega^2 lambda^2
sym_l2 = {n: cub(LAM2, n) for n in sf}
sym_ol2 = {n: cub(OML2, n) for n in sf}
sym_o2l2 = {n: cub(OM2L2, n) for n in sf}
print("gauss sums ready t", round(time.time() - t0, 1), flush=True)

E9 = cmath.exp(2j * math.pi / 9)


def brev(mu):
    return cmath.exp(4j * math.pi * mu.real)


# ---- dual coefficient lists: (ell, D(ell)) ----
D1, D2, D3 = [], [], []
for d in els:
    Nd = norm(d)
    if Nd ** 3 > NA_DUAL * 27:   # generous
        break
    vd = val(d)
    ad = math.sqrt(Nd)
    for c in sf:
        Nc = norm(c)
        base_norm = Nc * Nd ** 3
        if base_norm / 81 > NELL_MAX:
            break
        vc = val(c)
        cg = gval[c].conjugate()
        core = vc * vd ** 3
        # --- tau on lambda^{3n-4} families (n>=1) and lambda^{3n-3} (n>=0)
        n = 0
        while True:
            h = 3 * n - 3
            if 3.0 ** h * base_norm > NELL_MAX:
                break
            amp = 3 ** (n / 2 + 2.5) * ad * cg
            for sgn in (1, -1):
                ell = sgn * LAM ** h * core
                D1.append((ell, amp.conjugate()))       # conj tau(-ell) = conj tau(ell)
            n += 1
        n = 1
        while True:
            h = 3 * n - 4
            if 3.0 ** h * base_norm > NELL_MAX:
                break
            a0 = 3 ** (n / 2 + 2) * ad * cg
            vals = [(1, a0 * sym_l2[c]), (OM, a0 * E9.conjugate() * sym_ol2[c]), (OM * OM, a0 * E9 * sym_o2l2[c])]
            for u, tv in vals:
                for sgn in (1, -1):
                    ell = sgn * u * LAM ** h * core
                    D1.append((ell, tv.conjugate()))
            n += 1
        # --- tau_1, tau_2 (h=-4)
        if base_norm / 81 <= NELL_MAX:
            a0 = 9 * ad * cg
            t1 = [(1, a0 * OM * sym_l2[c]), (OM, a0 * E9.conjugate() * OM * OM * sym_ol2[c]), (OM * OM, a0 * E9 * sym_o2l2[c])]
            t2 = [(1, a0 * OM * OM * sym_l2[c]), (OM, a0 * E9.conjugate() * sym_ol2[c]), (OM * OM, a0 * OM * E9 * sym_o2l2[c])]
            for u, tv in t1:
                nu = u * LAM ** (-4) * core            # argument of tau_1
                mu = OM * nu                           # omega^2 * mu = nu  => mu = omega * nu
                d19 = OM * OM * tv * brev(mu)
                D2.append((-mu, d19.conjugate()))      # D_2(ell)=conj d_19(-ell), ell=-mu
            for u, tv in t2:
                nu = -u * LAM ** (-4) * core           # argument of tau_2
                mu = OM * OM * nu                      # omega * mu = nu => mu = omega^2 nu
                d10 = OM * tv * brev(mu)
                D3.append((-mu, d10.conjugate()))
print("dual lists", len(D1), len(D2), len(D3), "t", round(time.time() - t0, 1), flush=True)

# ---- kernel ----
tau = np.linspace(-9.0 / sigma, 9.0 / sigma, 1501)
dt = tau[1] - tau[0]
gaus = sigma * math.sqrt(2 * math.pi) * np.exp(-sigma ** 2 * tau ** 2 / 2)


def Rm(m):
    a1 = (m + 1) / 2 - 1 / 6
    a2 = (m + 1) / 2 + 1 / 6
    lg = loggamma(a1 + 1j * tau) + loggamma(a2 + 1j * tau) - loggamma(a1 - 1j * tau) - loggamma(a2 - 1j * tau)
    return np.exp(lg)


RM = {m: Rm(m) for m in range(0, 7)}


def vsharp(mk, xs):
    """Vsharp with kernel index mk at array of x"""
    xs = np.asarray(xs)
    ph = np.exp(-1j * np.outer(np.log(K * xs), tau))      # (Kx)^{-i tau}
    return (ph * (gaus * RM[mk])[None, :]).sum(axis=1) * dt / (2 * math.pi)


def dual_sum(lst, m, mk, X):
    ells = np.array([e for e, _ in lst])
    Ds = np.array([d for _, d in lst])
    N = np.abs(ells) ** 2
    al = ells / np.abs(ells)
    out = 0j
    # chunk to limit memory
    for i in range(0, len(lst), 4000):
        vs = vsharp(mk, N[i:i + 4000] * X)
        out += np.sum(Ds[i:i + 4000] * al[i:i + 4000] ** m / np.sqrt(N[i:i + 4000]) * vs)
    return out


def lhs(m, X):
    tot = 0j
    lo, hi = X * math.exp(-CUT * sigma), X * math.exp(CUT * sigma)
    for b in els:
        Nb = norm(b)
        if Nb ** 3 > hi:
            break
        vb3 = val(b) ** 3
        for n in sf:
            NA = norm(n) * Nb ** 3
            if NA > hi:
                break
            if NA < lo:
                continue
            A = val(n) * vb3
            w = math.exp(-(math.log(NA / X)) ** 2 / (2 * sigma ** 2)) / (math.sqrt(norm(n)) * Nb)
            tot += gval[n] * (A / abs(A)) ** (-m) * w
    return tot


print("%6s %3s %28s %28s %10s | wrong-kernel residuals (m'=m-1, m+1)" % ("X", "m", "LHS", "RHS", "|L-R|"))
checks=[]
for X in Xs:
    for m in MS:
        L = lhs(m, X)
        def rhs(mk):
            s = dual_sum(D1, m, mk, X) + OM * dual_sum(D2, m, mk, X) + OM * OM * dual_sum(D3, m, mk, X)
            return (-1j) ** m / 81 / 3 * s
        R = rhs(m)
        Rw1 = rhs(m - 1)
        Rw2 = rhs(m + 1)
        checks.append({"X":X,"mode":m,"error":float(abs(L-R)),"wrong_minus":float(abs(L-Rw1)),"wrong_plus":float(abs(L-Rw2))})
        print("%6.2f %3d %28s %28s %10.2e | %9.2e %9.2e" % (X, m, "%.9f%+.9fi" % (L.real, L.imag), "%.9f%+.9fi" % (R.real, R.imag), abs(L - R), abs(L - Rw1), abs(L - Rw2)), flush=True)
print("total time", round(time.time() - t0, 1))

assert max(x["error"] for x in checks)<1e-8
assert max(x["wrong_plus"] for x in checks)>1e-4
report={"status":"PASS","precision":"ordinary double precision; supplementary smoke check","checks":checks,"elapsed_seconds":round(time.time()-t0,3),"scope":"level-one primary mask; three actual cusp Fourier expansions; truncated sums and quadrature; no rigorous error enclosure"}
r=Path(__file__).parent/"results";r.mkdir(exist_ok=True);(r/"full_theta.json").write_text(json.dumps(report,indent=2))
