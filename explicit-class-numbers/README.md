# Explicit Littlewood-type bounds for L(1,χ) and class numbers from a zero-free half-plane

Jizhou Guo  
mitsuha2021b@gmail.com

Let 1/2 ≤ θ < 1 and let χ be a nonprincipal Dirichlet character modulo q ≥ 3 whose L-function has no zeros in Re(s) > θ. The paper proves, with every constant explicit, that

    ζ(2) e^(-γ) a e^(-Θ) / (M + log log q)  ≤  |L(1,χ)|  ≤  e^γ e^Θ (M + log log q) / a,      a = 22(1-θ)/25,

for every M ≥ 5, where Θ = Θ(θ, M, q) is an explicit small quantity (Θ < 0.0554 for θ = 7/8, M = 10). For θ = 7/8, the half-plane asserted for all Dirichlet L-functions by OpenAI's paper of 30 September 2026, this gives

    1/(10.41 (10 + log log q))  ≤  |L(1,χ)|  ≤  17.12 (10 + log log q),

and, for every fundamental discriminant -d < 0,

    h(-d) ≥ sqrt(d) / (32.69 (10 + log log d)),

so that h(-d) > 100 for d ≥ 1.83·10^9 and h(-d) > 1000 for d ≥ 1.88·10^11 (with a target-dependent choice of M: 1.15·10^9 and 1.17·10^11). The shape of the bounds is Littlewood's (1928, under GRH, for quadratic characters); Friedlander (1977, Pacific J. Math. 69) states that Littlewood's method extends to a zero-free half-plane, with the width entering the constants (he writes it for Legendre symbols to prime moduli and credits the lower bound to a remark of Elliott), and OpenAI's paper of 5 October 2026 notes the resulting bound h(D) ≫ sqrt|D|/log log|D| with an effective but unspecified constant. This paper gives explicit constants for this implication; they hold unconditionally exactly when the input theorem is correct, and the input is not verified here. A Hecke–Landau-type bound L(1,χ) ≥ 1/(120 log q) for real χ is also proved from the exclusion of real zeros in (1 - 1/(40 log q), 1) alone. The numerical section compares the thresholds with the unconditional determinations of Watkins (h ≤ 100) and Kimura (arXiv:2610.21511v2, h ≤ 2000, not yet refereed).

References to the OpenAI manuscripts use repository [openai/math](https://github.com/openai/math) at commit adc7f1241b42e322a6451854ab7e4b4c146bf78a:

- [The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf), September 30, 2026 (the input theorem).
- [The Quasi-Riemann Hypothesis](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-October-5-2026/paper2.pdf), October 5, 2026 (§1 remark on class numbers).
- [Uniform exclusion of Landau–Siegel zeros](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Uniform-exclusion-of-Landau-Siegel-zeros-October-1-2026/paper.pdf), October 1, 2026 (the input of Kimura's unconditional thresholds).
- [Lean scope document, lean/docs/003.md](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/docs/003.md).

The general theorem is also evaluated at the boundary σ† ≈ 0.874957 of [zero-free-beyond-7-8](https://github.com/aster2024/openai-math-followups/tree/main/zero-free-beyond-7-8) and at the [Quasi-Riemann Tracker](https://gtimg.github.io/QuasiRiemannTracker/) record 4369779/5000000 = 0.8739558 (J. Sussman, PR 86, 28 October 2026; not re-verified here); the gain is below one per cent because the constant is essentially e^γ/(ζ(2)a) with a proportional to the width 1 - θ.

Read [paper.pdf](paper.pdf). The complete LaTeX source is in [source/](source/). With Tectonic installed, compile from that directory:

    cd source
    tectonic main.tex

Alternatively, with pdfLaTeX: run `pdflatex main.tex`, `bibtex main`, and `pdflatex main.tex` twice.

From this directory, rerun the constant computations and the sanity checks with Python 3 (mpmath, numpy, scipy):

    python3 anc/constants.py
    python3 anc/checks.py

`constants.py` evaluates every constant of the paper (Tables 1 and 2) and the class-number thresholds; `checks.py` verifies the auxiliary inequalities numerically, recomputes h(-d) for d ≤ 3·10^6, and checks the bounds against |L(1,χ)| for all characters modulo primes q ≤ 1500. Their outputs are in anc/. The scripts check arithmetic; the proofs are in the paper.

## Use of AI

The proofs and the text of the paper were produced with AI systems (Claude Fable 5.1 and Claude Opus 5.5) under the author's direction. They were checked by independent reviews with AI models and by the computations in the ancillary files. No human expert has reviewed them. The author takes responsibility for the content.

## Citation

```bibtex
@misc{Guo2026Littlewood,
  author = {Guo, Jizhou},
  title = {Explicit {L}ittlewood-type bounds for {$L(1,\chi)$} and class numbers from a zero-free half-plane},
  year = {2026},
  month = oct,
  note = {28 October 2026}
}
```
