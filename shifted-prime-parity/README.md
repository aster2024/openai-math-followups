# Shifted primes with a prescribed parity of the number of prime factors

Jizhou Guo — mitsuha2021b@gmail.com — 9 October 2026

[**Paper (PDF, 31 pages)**](paper.pdf) · [LaTeX source](source/) · [Programs](anc/)

## Result

Let λ be the Liouville function. There are absolute constants c > 0 and X\* such that for every X ≥ X\*, every
integer h with 0 < |h| ≤ (log X)⁵ and each sign s ∈ {−1, +1},

```math
\#\{p\le X\ \text{prime}:\ p+h\gt 0,\ p+h\ \text{squarefree},\ \lambda(p+h)=s\}\ \ge\ c\,\frac{X}{(\log X)^{300}} .
```

Consequently, for every non-zero integer h there are infinitely many primes p with μ(p + h) = 1 and infinitely many
with μ(p + h) = −1: the number of prime factors of p + h is even for infinitely many primes p and odd for
infinitely many primes p, with p + h squarefree in both cases. For h = 2 this gives both parities of the number of
prime factors of p + 2.

The exponent 300 is not optimised and X\* is not effective.

## What the proof uses

Two papers of the [OpenAI mathematics release](https://github.com/openai/math), pinned to commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`:

- [E] [Prime Predecessors with an Even Number of Prime Factors](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Prime-Predecessors-with-an-Even-Number-of-Prime-Factors-September-17-2026/paper.pdf)
  (17 September 2026). Its Theorem 1.1 states that there are infinitely many primes p with p − 1 squarefree and
  Ω(p − 1) even.
- [S] [Weighted dilation graphs, smooth shifted primes and totient fibers](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Weighted-Dilation-Graphs-Smooth-Shifted-Primes-and-Totient-Fibers-September-24-2026/paper.pdf)
  (24 September 2026).

The theorem above is deduced from the following numbered statements, used as written, with their hypotheses
verified at each place of use: [E, Theorem 4.1] (prime-slot correlations), [E, Lemmas 2.4, 5.1, 8.3],
[S, Lemma 2.9], [S, Lemmas 7.3–7.4] with the estimates (7.13) and (7.20) from their proofs, and the classical
estimates collected in [E, Propositions 2.1–2.2]. Inside [E] and [S], the correlation theorem rests on
[E, Lemma 3.1] and on [S, Lemma 3.4, Theorem 3.5, Corollary 3.11, Theorem 4.1, Lemmas 4.2–4.3]. The zero-free
half-plane theorem of the same release is not used.

## Relation to [E]

The weight, the parity projection, the Type II argument and the prime extraction are those of [E], which uses the
projection A₀(1 − E)/2. The proof of [E, Theorem 6.1] treats the two terms A₀ and A₀E of this projection separately,
so it covers both projections A₀(1 ± E)/2, and the estimates of [E] give a lower bound of the shape X/(log X)^C for
the sign in [E, Theorem 1.1]. For h = ±1 the other sign and the shift +1 follow that argument with the sign of the
projection and the unit in p = 2u + 1 changed.

For a general shift the paper writes p = au + b with a ∈ {1, 2} and b = −h, and

- keeps the condition (e, R) = 1, R = rad(2a|b|), in the Cauchy–Schwarz majorant of the Type II sum, with the
  parametrisation m′ − m = aek, v′ − v = kn, mv′ − m′v = bk of the off-diagonal terms;
- writes this condition as the indicator of a set of units modulo a|k|R and expands it into Dirichlet characters
  of the rough variable;
- carries the local factor T(a, b) = ∏ (ℓ − 1)/(ℓ − 2), over odd primes ℓ dividing ab, through the sieve main term
  and the bound for balanced pairs, where it cancels when the width of the balanced range is chosen;
- keeps all estimates uniform for |h| ≤ (log X)⁵ and passes from window counts to every large X.

An appendix lists every place of [E, Sections 4–8] at which the shift, the coefficient 2 or a coprimality condition
enters, with the corresponding change.

## Background

Chen's theorem gives infinitely many primes p for which p + 2 is a prime or a product of two primes, without
specifying which. Goldston, Graham, Pintz and Yıldırım ([arXiv:0803.2636](https://arxiv.org/abs/0803.2636), 2008)
recorded as open the assertion that p + 2 has an odd (or even) number of prime factors for infinitely many primes p.
Pintz ([arXiv:1004.1065](https://arxiv.org/abs/1004.1065), 2010) proved that λ(p + d) = −1 for infinitely many
primes p for some even d with 0 < |d| ≤ 16.

## Files

Read [paper.pdf](paper.pdf). The LaTeX source is in `source/`; with Tectonic installed,

    cd source
    tectonic main.tex

or, with the included bibliography, run `pdflatex main.tex` twice.

The two programs in [`anc/`](anc/) check, on finite ranges, the algebraic identities of Section 2 (the bilinear
parametrisation, its inverse, and the description of the coprimality condition by residues modulo a|k|R) and the
local factors. They need only the Python 3 standard library:

    cd anc
    python3 general_parametrisation.py
    python3 general_local_conditions.py

`SHA256SUMS` records the distributed files.

## Citation

```bibtex
@misc{Guo2026ShiftedPrimeParity,
  author = {Guo, Jizhou},
  title = {Shifted primes with a prescribed parity of the number of prime factors},
  year = {2026},
  month = oct,
  howpublished = {\url{https://github.com/aster2024/openai-math-followups/tree/main/shifted-prime-parity}},
  note = {Preprint, 9 October 2026}
}
```
