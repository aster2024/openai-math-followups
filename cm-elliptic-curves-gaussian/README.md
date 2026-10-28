# A zero-free half-plane for angular Hecke L-functions over Q(i) and for the elliptic curves y² = x³ − Dx

Jizhou Guo — mitsuha2021b@gmail.com — 24 October 2026

[**Paper (PDF, 35 pages)**](paper.pdf) · [LaTeX source](source/) · [Checks of explicit identities](anc/)

## Results

Let K = Q(i). A unitary Hecke character η of K of conductor f has *angular type* k if

    η((z)) = (z/|z|)^k · N(z)^(it₀)    for z ≡ 1 (mod f),    k an integer, t₀ real.

The L-function L_K(s, η) is normalized with functional equation centred at 1/2. Characters of angular type k ≠ 0
have infinite order.

**Theorem A.** Every unitary Hecke character η of K of finite conductor and non-zero angular type satisfies

    L_K(s, η) ≠ 0    for Re s > 11/12.

The half-plane is the same for every conductor, every angular type and every t₀. For an algebraic Hecke character of
infinity type (a, b) with a ≠ b the corresponding half-plane is Re s > (a + b)/2 + 11/12.

**Theorem B.** For every non-zero rational number D, the L-function of the elliptic curve E_D : y² = x³ − Dx
satisfies

    L(E_D, s) ≠ 0    for Re s > 17/12

in the arithmetic normalization, in which the functional equation has centre s = 1. Consequently the non-trivial
zeros of L(E_D, s) lie in the strip 7/12 ≤ Re s ≤ 17/12. The curves E_D are the elliptic curves over Q with
j-invariant 1728; they include the congruent number curves y² = x³ − n²x.

*CM newforms.* Every holomorphic newform of weight w ≥ 2 attached to an algebraic Hecke character of K of infinity
type (w − 1, 0), of any conductor, has L-function zero-free for Re s > (w − 1)/2 + 11/12 in the arithmetic
normalization.

**Applications.**

- *Gaussian primes in sectors.* The number of odd prime ideals of Z[i] of norm at most x whose primary generator
  (π ≡ 1 mod (1 + i)³) has argument in an arc J is (|J|/2π)·Li(x) + O(x^(11/12+ε)), uniformly in J.
- *Distribution of a_p(E_D).* For fixed D, the number of good primes p ≤ x with a_p(E_D)/(2√p) in an interval I is
  μ(I)·Li(x) + O(x^(11/12+ε)), uniformly in I, where μ is half the point mass at 0 plus dt/(2π√(1 − t²)) on [−1, 1].
- *Symmetric powers.* For every n ≥ 1, L(Symⁿ E_D, s) ≠ 0 for Re s > n/2 + 11/12.

## What the proof uses

- OpenAI, [*The Quasi-Riemann Hypothesis*](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-October-5-2026)
  (5 October 2026), whose cubic-theta method for finite-order characters the paper follows. Its smooth-kernel
  Lemmas B.1–B.3 (Appendix B) are used as printed.
- OpenAI, [*Primitive roots for every admissible integer base*](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf)
  (4 October 2026), whose cubic-theta construction over cyclotomic fields supplies the normalization. The
  finite-field Gauss inversion, Gauss–Jacobi and duplication identities of its Lemma 3.4 are used as printed; the
  field-dependent statements it contains are proved in the paper for the field needed here.
- Classical results: Hecke's theory of L-functions of Grössencharacters and the prime ideal theorem, class field
  theory, the cubic theta function of Kazhdan and Patterson (*Metaplectic forms*, 1984, with the corrections of
  1985), the quadratic large sieve of Goldmakher and Louvel, and Deuring's theorem for CM elliptic curves.
- OpenAI's half-plane Re s > 7/8 for Dirichlet L-functions
  ([30 September 2026](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf),
  Theorem 1.1), for the finite-order factors in the applications.

All OpenAI manuscripts are cited at commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`. Neither of the first two is
formalized; the paper lists the statements used as printed, with their hypotheses.

The proof passes to the field F = Q(ζ₁₂) = Q(i, √3). With χ the quadratic character of F/K,
L_F(s, η∘N_{F/K}) = L_K(s, η)·L_K(s, ηχ), with all Euler factors including those at 2 and 3. Both factors are entire
when k ≠ 0, so zero-freeness of the product gives it for each factor. The lifted character has angular type (k, k)
at the two complex places of F; combined with the cubic Gauss sums, whose type is (1, −1), it gives the angular
modes (r − 1, r + 1) of the cubic theta function over F. The paper derives the normalized theta coefficients,
the reflection on annuli, a labelled mean square, and the two Poisson transformations over complete orbits of
sixth powers of S-units, which over F form an infinite group. A cube inversion and a finite descent then give the
half-plane. For Theorem B the paper writes down the Hecke character of E_D and its conductor for every rational D,
and applies Deuring's theorem, L(E_D, s) = L_K(s − 1/2, η_D) with η_D unitary of angular type 1.

## Related work

The author's paper [`cm-elliptic-curves/`](../cm-elliptic-curves/) (8 October 2026) proves the corresponding
statements for Q(√−3) and the curves y² = x³ + D; the present paper follows its notation and organization where the
arguments run in parallel. B. Yates ([Zenodo, 7 and 8 October 2026](https://doi.org/10.5281/zenodo.23228131)) states
the Q(√−3) results, assuming that the argument of OpenAI's 11/12 paper is correct.

A draft dated 8 October 2026 in the repository
[Rogerhu12/openai-math-extensions](https://github.com/Rogerhu12/openai-math-extensions/blob/a4a1eb9e45b38d50c39afb9c35f582e8786ce262/papers/029-artin-primitive-roots/hecke_seven_eighths_all_characters.pdf),
*A seven-eighths theorem for Hecke characters over arbitrary number fields*, states the half-plane Re s > 7/8 for every
continuous unitary Hecke character of every number field, under its Source Input 1.1 on the constructions and
analytic arguments of the OpenAI papers; the characters of Theorem A are among those it covers. It transfers between
fields and works with finite-order twists of a character and of its conjugate.

B. Hu's subsequent paper, [*A seven-eighths zero-free half-plane for unitary Weil L-functions*](https://hexagonmath.org/2610.00216v1)
(Hexagon 2610.00216v1, 13 October 2026), supersedes that draft. Its Theorem 1.2 states the half-plane Re s > 7/8 for every
unitary Hecke character of every number field, including characters of infinite order and hence the characters of
Theorem A; its field and infinity-type transfer has not been independently verified here.

For finite-order characters, B. Liu ([arXiv:2610.12234v2](https://arxiv.org/abs/2610.12234v2)) and Y. Xu and H. Sang
([arXiv:2610.15291v2](https://arxiv.org/abs/2610.15291v2)) state boundaries slightly below 7/8 for Dirichlet
characters and for finite-order characters of Q(√−3), and B. Liu ([arXiv:2610.26835v1](https://arxiv.org/abs/2610.26835v1)) states
one for finite-order characters of every number field. The classical zero-free regions for Hecke L-functions of
non-zero angular type, such as Coleman's, approach the line Re s = 1.

## Files

| Path | Content |
|---|---|
| `paper.pdf` | The paper |
| `source/main.tex`, `source/references.bib`, `source/main.bbl` | LaTeX source (Tectonic or pdfLaTeX) |
| `anc/` | Programs checking explicit identities exactly or to high precision; see [`anc/README.md`](anc/README.md) |
| `SHA256SUMS` | Checksums of the files above |

## Citation

```bibtex
@misc{Guo2026HeckeGaussian,
  author = {Guo, Jizhou},
  title = {A zero-free half-plane for angular {H}ecke {$L$}-functions over {$\mathbb{Q}(i)$} and for the elliptic curves {$y^2=x^3-Dx$}},
  year = {2026},
  month = oct,
  howpublished = {\url{https://github.com/aster2024/openai-math-followups/tree/main/cm-elliptic-curves-gaussian}},
  note = {Preprint, 24 October 2026}
}
```
