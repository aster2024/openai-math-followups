# The Möbius function at N − p

Jizhou Guo — mitsuha2021b@gmail.com — 22 October 2026

[**Paper (PDF, 40 pages)**](paper.pdf) · [LaTeX source](source/) · [Programs](anc/)

## Result

The statements are conditional on the arguments of the preprint of G. Lü, Z. Wang and J. Wu
([arXiv:2610.20242v1](https://arxiv.org/abs/2610.20242v1), 14 October 2026; cited below as LWW). The paper calls H2′ the
assertion that the arguments of LWW Sections 4.2–4.7, including the proofs of Propositions 4.2–4.5, and of Appendix A,
(A.2)–(A.4), are correct as written. Put

```math
A_N=\prod_{p\nmid N}\Bigl(1-\frac{1}{p(p-1)}\Bigr).
```

**Goldbach shift.** Assume H2′ and that no Dirichlet L-function has a zero with Re s > 7/8. Then, as N → ∞ through
even integers,

```math
\sum_{p<N}\mu(N-p)=o(\pi(N)),\qquad \#\{p<N:\ \mu(N-p)=\kappa\}=\Bigl(\frac{A_N}{2}+o(1)\Bigr)\pi(N)\quad(\kappa=\pm1).
```

The half-plane enters only through a zero-free region of width C₁ log log N/log N up to height (log N)^C₂, for the
primitive characters whose conductor divides kN with k ≤ (log N)^A₀ and exceeds (log N)^A₁.

**Small radical.** Assume H2′ only. For each fixed C, the same conclusions hold as N → ∞ through even integers with
rad(N) ≤ (log N)^C. Here Iwaniec's zero-free region of 1974 and Burgess's bound supply the analytic input.

**Small shifts.** Assume H2′ and, in addition, LWW Sections 2.3, 3, 5 and 6 as written. For each fixed C, uniformly
in integers h with 0 < |h| ≤ (log x)^C,

```math
\sum_{\substack{p\le x\\ p+h\ge 1}}\mu(p+h)=o(\pi(x)),\qquad \#\{p\le x:\ p+h\ge1,\ \mu(p+h)=\kappa\}=\Bigl(\frac{A_h}{2}+o(1)\Bigr)\pi(x)\quad(\kappa=\pm1).
```

**Liouville function.** Under the respective hypotheses, each statement holds with λ in place of μ and with each sign
density 1/2 + o(1).

All error terms are ineffective. In the first two statements they are uniform in N within the stated class.

## What the proof uses

- From LWW, as numbered inputs: Propositions 2.1–2.3 with (2.5) and (2.11), Proposition 3.1 with (3.1), (3.4) and
  (3.5), Lemma 4.1 with (4.6), and Proposition 6.1 with (6.3). The arguments of Sections 4.2–4.7 and Appendix A are
  used as written after the changes listed in the paper's appendix; this is the assumption H2′. The small-shift
  statement also uses Lemmas 5.1–5.2 and the proof of Proposition 5.3.
- For the Goldbach shift, the zero-free half-plane Re s > 7/8 of OpenAI's paper
  [The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf)
  (30 September 2026, Theorem 1.1, p. 4), pinned to commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
- For the small-radical class, Theorem 2 of H. Iwaniec, *On zeros of Dirichlet's L series* (Invent. Math. 23 (1974), p. 97),
  and the Burgess bound with r = 2 for arbitrary moduli in the form stated by D. R. Heath-Brown
  ([arXiv:1203.5219](https://arxiv.org/abs/1203.5219)).

## Changes to the argument of LWW

LWW treat the shift 2. For the shift N the paper

- decomposes the endpoint support of the determinant congruence into blocks on the unit-coordinate chart of
  ℙ¹(ℤ/Nℤ), using that det(g_N z, g_N z′) = N·det(z, z′) in a basis of each lattice of index N;
- replaces the matrix diag(1, −2) of LWW by E_N = diag(1, N), followed by an integral shear;
- proves a root count with both coordinates units modulo N and with the normalized complementary ratio;
- reduces the major arcs to a character-averaged energy at polylogarithmic height and bounds it from the zero-free
  inputs above;
- in the Type I estimate, extracts the common divisor (r, N) before applying the Möbius identity.

An appendix lists every change by LWW section, equation and page. The paper also records a configuration of a real
character modulo a divisor of N under which |Σ_{p<N} μ(N − p)| ≥ 0.27·π(N) (Proposition EC); it explains a limitation
of the classical zero-free inputs for this method.

## Background

LWW state in Theorem 1 that Σ_{p≤x} μ(p + 2) = o(π(x)), and in Theorem 2 that each of μ(p + 2) = 1 and μ(p + 2) = −1
has asymptotic density 1/2 among the primes p with p + 2 squarefree. Their abstract describes the conjecture as
dating back at least to Hildebrand's work in 1989. Their Section 4.4 describes the construction of their auxiliary
operators as similar to Sections 4.1–4.3 of OpenAI's paper
[The Poisson–Dirichlet law for prime predecessors](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Poisson-Dirichlet-Law-for-Prime-Predecessors-September-24-2026)
(24 September 2026), and their Appendix A says that its root-counting proof follows the argument of Lemma 3.3 of that
paper.

The author's papers [`shifted-prime-parity/`](../shifted-prime-parity/) and
[`rough-goldbach-parity/`](../rough-goldbach-parity/) in this repository concern the Liouville signs of p + h and of
pairs of rough numbers with sum N.

## Files

Read [paper.pdf](paper.pdf). The LaTeX source is in `source/`; with Tectonic installed,

    cd source
    tectonic main.tex

or, with the included bibliography, run `pdflatex main.tex` twice.

The two programs in [`anc/`](anc/) check finite instances of the block algebra (determinant transport, line and
block counts, the parity condition, the nonnegative square and the conjugation of coefficients) and of the root
count and local factors. They need only the Python 3 standard library:

    cd anc
    python3 check_blocks.py
    python3 check_roots.py

They do not verify the asymptotic estimates, the arguments of LWW, the zero-free inputs or the main statements.
`SHA256SUMS` records the distributed files.

## Citation

```bibtex
@misc{Guo2026MobiusGoldbachShift,
  author = {Guo, Jizhou},
  title = {The {M\"obius} function at {$N-p$}},
  year = {2026},
  month = oct,
  howpublished = {\url{https://github.com/aster2024/openai-math-followups/tree/main/mobius-goldbach-shift}},
  note = {Preprint, 22 October 2026}
}
```
