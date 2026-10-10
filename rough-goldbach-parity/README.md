# Sums of two rough numbers with prescribed Liouville signs

Jizhou Guo — mitsuha2021b@gmail.com — 9 October 2026

[**Paper (PDF, 23 pages)**](paper.pdf) · [LaTeX source](source/) · [Programs](anc/)

## Result

Let λ be the Liouville function and write P⁻(n) for the least prime factor of n. There are absolute constants
c > 0 and N₀ such that for every even integer N ≥ N₀ and each pair of signs (σ, τ),

```math
\#\{\,n:\ N/3\le n\le 2N/3,\ \ P^-(n)\gt z,\ \ P^-(N-n)\gt z,\ \ \lambda(n)=\sigma,\ \ \lambda(N-n)=\tau\,\}\ \ge\ c\,\frac{N}{(\log N)^{1/4}},
\qquad z=\exp\bigl((\log N)^{1/10}\bigr).
```

The same holds, with a possibly smaller constant c, when n and N − n are also required to be squarefree with at
most ⌈2 log log N⌉ prime factors.

The number of n ∈ [N/3, 2N/3] with both n and N − n free of prime factors below z has order 𝔖(N)·N/(log N)^(1/5),
where 𝔖(N) is the singular series of the binary Goldbach problem. N₀ is not effective. The bound ⌈2 log log N⌉
grows with N; the paper makes no statement for a fixed number of prime factors or for prime summands.

## What the proof uses

From the [OpenAI mathematics release](https://github.com/openai/math), pinned to commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`:

- the zero-free half-plane Re s > 7/8 for all Dirichlet L-functions (family 003;
  `OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re` in the Lean library), in the same form as in
  [`liouville-goldbach/`](../liouville-goldbach/);
- [S] [Weighted dilation graphs, smooth shifted primes and totient fibers](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Weighted-Dilation-Graphs-Smooth-Shifted-Primes-and-Totient-Fibers-September-24-2026/paper.pdf)
  (24 September 2026): Definitions 3.1–3.3, Lemmas 3.4 and 3.6, Theorem 3.5, Corollary 3.11, Theorem 4.1 and
  Lemma 4.2.

Two of the graph estimates are needed in a form that [S] does not state: for displacements that are multiples of
N (in [S] the displacement is kD with |k| at most a fixed power of log x), and for prime groups from
which the prime factors of N have been removed. Proposition 2.5 and Proposition 2.7 of the paper obtain these from
the proofs in [S] rather than from its statements; their proofs go through every place of [S, Section 3] where the
displacement enters and every place of [S, Section 4] where a group is used as a full interval of primes.

The shared-label sign cancellation follows Section 4 of OpenAI's
[Prime Predecessors with an Even Number of Prime Factors](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Prime-Predecessors-with-an-Even-Number-of-Prime-Factors-September-17-2026/paper.pdf)
(17 September 2026).

## Method

The summands carry shared prime labels in a weighted graph on the integers; the labels are removed by complete
multiplicativity, λ(Dw)·λ(Dw′) = λ(w)·λ(w′), which returns the same total N. Reflection n ↦ N·D − n is the
composition of a dilated displacement with n ↦ −n. The comparison terms of the graph estimate live on rational
frequencies with denominators Nr; character orthogonality keeps the factor 1/(Nr), and the zero-free half-plane
bounds the short prime sums with non-principal characters of modulus Nr.

## Related results

Sign patterns of (λ(n), λ(N − n)) with no condition on the prime factors of the summands: the asymptotic count
N/4 + O(N/(log N)^c) of each pattern for every large N ([`liouville-goldbach/`](../liouville-goldbach/)); at
least c_ε N^(1−ε) representations of each pattern for every large N (Pouly,
[doi:10.5281/zenodo.22959603](https://doi.org/10.5281/zenodo.22959603), 25 September 2026); all four patterns for
every N ≥ 11 (Meng); the pattern (−1, −1) for every even N > 2 (CaptainSude) and, under GRH, for all large even N
(Mangerel, arXiv:2412.17199). Chen-type theorems bound the number of prime factors of the summands without
prescribing both parities. A bound for sifted versions of the reflected two-point sum, with sifting level a power of N, is
stated as a hypothesis by Deligiannis ([doi:10.5281/zenodo.21581938](https://doi.org/10.5281/zenodo.21581938),
2026) and as the remaining analytic problem of a programme on the binary Goldbach problem by Arneth
([doi:10.5281/zenodo.23011047](https://doi.org/10.5281/zenodo.23011047), September 2026). The companion paper for a
fixed difference is [`rough-pairs-fixed-distance/`](../rough-pairs-fixed-distance/).

## Files

Read [paper.pdf](paper.pdf). The LaTeX source is in `source/`; with Tectonic installed,

    cd source
    tectonic main.tex

or, with the included bibliography, run `pdflatex main.tex` twice.

The two programs in [`anc/`](anc/) check finite instances of the algebraic identities used in the paper:

    cd anc
    python3 reflected_identities.py
    python3 rough_convolution.py

`SHA256SUMS` records the distributed files.

## Citation

```bibtex
@misc{Guo2026RoughGoldbachParity,
  author = {Guo, Jizhou},
  title = {Sums of two rough numbers with prescribed {L}iouville signs},
  year = {2026},
  month = oct,
  howpublished = {\url{https://github.com/aster2024/openai-math-followups/tree/main/rough-goldbach-parity}},
  note = {Preprint, 9 October 2026}
}
```
