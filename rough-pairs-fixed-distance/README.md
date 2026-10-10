# Rough numbers at a fixed distance with prescribed Liouville signs

Jizhou Guo — mitsuha2021b@gmail.com — 10 October 2026

[**Paper (PDF, 38 pages)**](paper.pdf) · [LaTeX source](source/) · [Programs](anc/)

## Results

Let λ be the Liouville function, P⁻(n) the least prime factor of n, and h ≥ 2 a fixed even integer. Put
V_h(z) = ∏_{p ≤ z} (1 − ν_h(p)/p), with ν_h(p) = 1 if p divides h and 2 otherwise.

**Theorem 1.1.** There is an absolute constant γ > 0 such that, for every sufficiently large X, uniformly for
2 ≤ z ≤ exp((log X)^(1/3750)) and for each of the four sign patterns (s, t),

```math
\#\{\,n\le X:\ P^-(n)\gt z,\ P^-(n+h)\gt z,\ (\lambda(n),\lambda(n+h))=(s,t)\,\}
=\tfrac14\,X\,V_h(z)\,\bigl(1+O_h((\log X)^{-\gamma})\bigr).
```

Here X·V_h(z) is the main term for the number of n ≤ X with n and n + h free of prime factors up to z; at the top of
the range it is of order X/(log X)^(2/3750).

**Theorem 1.2.** Each sign pattern occurs for ≫ X/(log X)^(1/1875) integers n ≤ X such that n and n + h are
squarefree, have no prime factor up to exp((log X)^(1/3750)), and have at most (1 − 1/4000)·log log X prime factors.

**Theorem 1.3.** The analogue of Theorem 1.1 for the weight r^(ω_z(n)) on the prime factors up to z (0 < r < 1
fixed), with squarefreeness imposed at the primes up to z.

**Theorem 1.4.** For a weight r^(Ω(n)) on all prime factors, with r close to 1 and squarefreeness imposed at small
primes, the three signed sums of λ(n), λ(n + h) and λ(n)λ(n + h) against the weight are smaller than the unsigned
mass by a power of log X.

The shift h is fixed; there is no exceptional set of X. All constants and thresholds are ineffective. The bound
on the number of prime factors in Theorem 1.2 grows with X; the paper makes no statement for a fixed number of
prime factors or for primes.

## What the proof uses

OpenAI's paper proving the two-point Chowla conjecture (family 007 of the
[OpenAI mathematics release](https://github.com/openai/math), pinned to commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`), which the paper calls [O].

- Used as stated, with hypotheses verified in the paper: [O, Lemma 5.5], [O, Lemmas 6.1, 6.3–6.4, 7.1–7.2] and the
  finite-dimensional transfer [O, Lemma 8.1].
- Not applicable as stated, because the operator is changed (padding weight 16^ω, vertex weight 17^(ω_Q), a
  roughness condition on the target vertex inside the padding probability, soft and full-Ω weights): the moment
  bound [O, Theorem 5.4] and the lemmas around it. The paper states the versions it needs and proves them by going
  through the proofs of [O] step by step, with page references. The finite comparison of [O, Section 3] is replaced
  by a separate argument based on bounded independence (Bazzi, Razborov, Braverman).
- Classical inputs: the Matomäki–Radziwiłł–Tao distance bound, the fundamental lemma of the sieve, the
  Bombieri–Vinogradov theorem for λ over all residue classes, theorems of Shiu and Nair–Tenenbaum, and Halász's
  theorem.

The zero-free half-plane Re s > 7/8 of the same release is not used. The classical zero-free region enters through
the cited distance bound.

## Related work

- Preobrazhenskiĭ and Preobrazhenskaya ([arXiv:1405.0682](https://arxiv.org/abs/1405.0682), Conjecture 2)
  conjectured cancellation in two-point sums of μ with weights κ₁^(ω⁻(n,y)) κ₂^(ω⁺(n,y)), y = exp((log x)^δ), and
  state that the conjecture essentially implies the twin prime conjecture. The weights of Theorems 1.1 and 1.3 have
  this shape with κ₂ = 1; the theorems are for λ and hold for z ≤ exp((log X)^(1/3750)).
- Truncated functions, which record only the prime factors up to y: Cassaigne–Ferenczi–Mauduit–Rivat–Sárközy
  (1999), Daboussi–Sárközy (2003), Mangerel ([arXiv:1612.09544](https://arxiv.org/abs/1612.09544)).
- Two-point correlations without sieve conditions: Tao ([arXiv:1509.05422](https://arxiv.org/abs/1509.05422)),
  Tao–Teräväinen ([arXiv:1809.02518](https://arxiv.org/abs/1809.02518),
  [arXiv:2512.01739](https://arxiv.org/abs/2512.01739)), Pilatte
  ([arXiv:2310.19357](https://arxiv.org/abs/2310.19357)), Charamaras–Richter
  ([arXiv:2412.17583](https://arxiv.org/abs/2412.17583)), Hughes
  ([arXiv:2609.28526](https://arxiv.org/abs/2609.28526)), and [O] itself.
- Prescribed values of Ω at a fixed gap and restrictions on Ω: Goldston–Graham–Pintz–Yıldırım
  ([arXiv:0803.2636](https://arxiv.org/abs/0803.2636)), Helfgott–Radziwiłł
  ([arXiv:2103.06853](https://arxiv.org/abs/2103.06853)), Matomäki–Radziwiłł–Tao
  ([arXiv:1509.01545](https://arxiv.org/abs/1509.01545)).
- Formal statements at specific small sieve levels (n(n + 2) free of prime factors up to z ≤ 10 with an odd number
  of prime factors, infinitely often in each admissible class): the Lean 4 repository
  [jyh/salt](https://github.com/jyh/salt), September 2026.
- The sifted sum of λ(n)λ(n + 2) at sieve level N^(1/8), in a conditional approach to twin primes: McCaffer
  ([doi:10.5281/zenodo.20388364](https://doi.org/10.5281/zenodo.20388364), May 2026).

The companion paper for sums, [`rough-goldbach-parity/`](../rough-goldbach-parity/), treats n and N − n.

## Files

Read [paper.pdf](paper.pdf). The LaTeX source is in `source/`; with Tectonic installed,

    cd source
    tectonic main.tex

or, with the included bibliography, run `pdflatex main.tex` twice.

The two programs in [`anc/`](anc/) check finite instances of the algebraic identities and encodings used in the
paper (Python 3 standard library only):

    cd anc
    python3 arithmetic_identities.py
    python3 comparison_identities.py

`SHA256SUMS` records the distributed files.

## Citation

```bibtex
@misc{Guo2026RoughPairsFixedDistance,
  author = {Guo, Jizhou},
  title = {Rough numbers at a fixed distance with prescribed {L}iouville signs},
  year = {2026},
  month = oct,
  howpublished = {\url{https://github.com/aster2024/openai-math-followups/tree/main/rough-pairs-fixed-distance}},
  note = {Preprint, 10 October 2026}
}
```
