# A zero-free half-plane for Hecke L-functions of infinite order over Q(√−3) and for cubic CM elliptic curves

Jizhou Guo — Dots Studio, Rednote — mitsuha2021b@gmail.com — 8 October 2026

[**Paper (PDF, 30 pages)**](paper.pdf) · [LaTeX source](source/) · [Checks of explicit identities](anc/)

## Results

Let K = Q(√−3). A unitary Hecke character η of K of conductor f has *angular type* k if

    η((z)) = (z/|z|)^k · N(z)^(it₀)    for z ≡ 1 (mod f),    k an integer, t₀ real.

The degree-two L-function L_K(s, η) is normalized with functional equation centred at 1/2. Characters of angular
type k ≠ 0 have infinite order.

**Theorem A.** Every unitary Hecke character η of K of finite conductor and non-zero angular type satisfies

    L_K(s, η) ≠ 0    for Re s > 11/12.

The half-plane is the same for every conductor, every angular type and every t₀. For an algebraic Hecke character of
infinity type (a, b) with a ≠ b the corresponding half-plane is Re s > (a + b)/2 + 11/12.

**Theorem B.** For every non-zero rational number D, the L-function of the elliptic curve E_D : y² = x³ + D satisfies

    L(E_D, s) ≠ 0    for Re s > 17/12

in the arithmetic normalization, in which the critical strip is 1/2 < Re s < 3/2 and the centre is s = 1.

**Applications**, each with error term O(x^(11/12+ε)):

- *Eisenstein primes in sectors.* The number of prime ideals of norm at most x whose primary generator has argument
  in an arc J is (|J|/2π)·Li(x) + O(x^(11/12+ε)), uniformly in J.
- *Sato–Tate distribution for E_D.* For fixed D, the number of good primes p ≤ x with a_p(E_D)/(2√p) in an interval I
  is μ(I)·Li(x) + O(x^(11/12+ε)), uniformly in I, where μ is half the point mass at 0 plus dt/(2π√(1 − t²)) on [−1, 1].
- *Symmetric powers.* For every n ≥ 1, L(Symⁿ E_D, s) ≠ 0 for Re s > n/2 + 11/12.

*CM newforms.* Every newform of weight w ≥ 2 with complex multiplication by Q(√−3), of any level, has L-function
zero-free for Re s > (w − 1)/2 + 11/12 in the arithmetic normalization.

## What the proof uses

- OpenAI, [*The Quasi-Riemann Hypothesis*](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-October-5-2026)
  (5 October 2026), which proves the half-plane Re s > 11/12 for finite-order characters, at commit
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`. Its finite arithmetic and smooth-kernel statements listed in Section 2
  of the paper are used as printed.
- Classical results: the Kubota–Patterson cubic theta function and its Fourier coefficients at the cusps, cubic
  reciprocity, the quadratic large sieve of Goldmakher and Louvel, Hecke's theory of L-functions of
  Grössencharacters, and Deuring's theorem for CM elliptic curves.
- OpenAI's half-plane Re s > 7/8 for finite-order characters, for the finite-order factors and the zero-frequency
  terms in the applications.

A Gauss–Jacobi identity converts a target of angular type k into the angular mode k + 1 of the theta function. The
paper obtains every positive mode from pure Wirtinger derivatives of the cubic theta function at all cusps, proves
the Mellin reflection in an arbitrary positive mode, and carries the angular factor through the completed mean
square, the two Poisson transformations, the cube inversion and the descent; all steps involving the angular type
are derived in the paper.

## Files

| Path | Content |
|---|---|
| `paper.pdf` | The paper |
| `source/main.tex`, `source/references.bib`, `source/main.bbl` | LaTeX source (Tectonic or pdfLaTeX) |
| `anc/` | Programs checking explicit identities exactly or to high precision, with their outputs; see [`anc/README.md`](anc/README.md) |
| `SHA256SUMS` | Checksums of the files above |

## Citation

```bibtex
@misc{Guo2026HeckeInfiniteOrder,
  author = {Guo, Jizhou},
  title = {A zero-free half-plane for {H}ecke {$L$}-functions of infinite order over {$\mathbb{Q}(\sqrt{-3})$} and for cubic {CM} elliptic curves},
  year = {2026},
  month = oct,
  howpublished = {\url{https://github.com/aster2024/openai-math-followups/tree/main/cm-elliptic-curves}},
  note = {Preprint, 8 October 2026}
}
```
