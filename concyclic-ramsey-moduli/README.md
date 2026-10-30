# Concyclic Euclidean Ramsey sets with three-dimensional moduli

Jizhou Guo — mitsuha2021b@gmail.com — 23 October 2026

[**Paper (PDF, 17 pages)**](paper.pdf) · [LaTeX source](source/) · [Exact arithmetic checks](anc/)

## Results

For a finite set A of points on a circle, let M(A) be the field generated over Q by the four-point cross ratios of
the points, computed in any projective parametrization of the circle. A group of at least three of the points is
called *projectively algebraic* if all four-point cross ratios inside the group are algebraic over Q (for three
points the condition is empty).

**Theorem A.** Let A consist of n ≥ 7 distinct points on a circle with trdeg_Q M(A) = 3. Then A is Euclidean Ramsey
if and only if its points can be split into two projectively algebraic groups, each of at least three points.

**Corollary B.** Seven distinct points on a circle with trdeg_Q M(A) = 3 form a Ramsey set if and only if some
four-point cross ratio among them is algebraic over Q.

**Corollary C.** Let x, y, z be real numbers algebraically independent over Q. The seven points on the unit circle
with stereographic parameters

```math
-2,\quad 0,\quad 2,\quad x,\quad y,\quad -4-x-2y,\quad z
```

do not form a Ramsey set. This is the family s₃ = −4 − s₁ − 2s₂ discussed in Appendix E of D. Pálvölgyi,
*A cyclic non-Ramsey heptagon* ([arXiv:2609.23327v1](https://arxiv.org/abs/2609.23327v1)), whose Ramsey status is left
open there. The paper gives two proofs: one from Corollary B, since every four-point cross ratio of the family is
transcendental, and one by an explicit non-zero 10 × 10 minor of the second-order node equations.

**Theorem D.** An explicit seven-point family built from the curve y² = x³ − 2 (one transcendental real parameter)
is Ramsey, has moduli of transcendence degree one, and has all 35 four-point cross ratios transcendental. It
shows that the dimension hypothesis cannot simply be dropped from the necessary direction of Corollary B. Ramsey
seven-point sets with no algebraic cross ratio were already exhibited, by simpler rational families, in Section 7 of
W. Strinz's *spherical-ramsey* note cited below.

## What the proofs use

- OpenAI, *A classification of finite Euclidean Ramsey configurations*
  ([paper](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-classification-of-finite-Euclidean-Ramsey-configurations-September-23-2026/paper.pdf),
  result 172, 23 September 2026), Theorem 1.1, pinned to commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`. Every
  positive Ramsey conclusion (the "if" direction of Theorem A and Corollary B, and Theorem D) uses its sufficient
  direction.
- The necessary direction of Theorem A and Corollary B, and Corollary C, use neither direction of that theorem. The
  paper includes a self-contained proof that a set without a tensor certificate in its coordinate field is not Ramsey
  (by separation and an explicit colouring with at most (2n + 1)ⁿ colours in every dimension), following the mechanism
  of Section 2 of OpenAI's paper.
- The necessary direction rests on a second-order expansion of the tensor equations along the derivations of the
  moduli field, and on a classification of three-dimensional subspaces that are totally isotropic for the forms
  Σᵢ tᵢˡ uᵢ vᵢ / H′(tᵢ), H(T) = ∏(T − tᵢ): on seven or more nodes they are the sign-twisted spaces of quadratic
  evaluations.

## Related public work

- The "if" direction of Theorem A is a circle case of the two-group theorem (Theorem C2) of W. Strinz,
  *Two Möbius groups suffice: Euclidean Ramsey sets on spheres of every dimension, after the tensor classification*
  (spherical-ramsey v1.1.0, 15 October 2026, [doi:10.5281/zenodo.23396387](https://doi.org/10.5281/zenodo.23396387)),
  which also uses OpenAI's sufficient direction.
- Every set of at most six points on a circle is Ramsey: JD Jones's tensor certificate for six concyclic points
  ([six-concyclic-lean](https://github.com/JD-Jones-ASES/six-concyclic-lean), 7 October 2026) combined with OpenAI's
  sufficient direction; also Theorem B(a) of Strinz's note, with a Lean development.
- Pálvölgyi's Theorem A.3: seven circle points whose last four parameters are algebraically independent over the field
  of the first three are not Ramsey. It does not apply to the family of Corollary C.
- W. Strinz, *Ramsey-ness of finite spherical sets is Möbius invariant* (mobius-ramsey v1.0.0, 13 October 2026,
  [doi:10.5281/zenodo.23339523](https://doi.org/10.5281/zenodo.23339523)).
- A. R. Towell, *Exact rotational moments and a triangular-base tensor obstruction (Family 172)* (24 October 2026,
  [doi:10.5281/zenodo.23613220](https://doi.org/10.5281/zenodo.23613220)): a nine-point tensor obstruction built from
  three equilateral triangles, with one transcendental parameter; its non-Ramsey consequence is stated conditional on
  the source classification. It does not address the transcendence-degree-three classification proved here.

## Ancillary files

[`anc/`](anc/) contains five Python programs (exact rational arithmetic with SymPy) for the explicit identities and
finite certificates used in the paper, and a validator that compares the matrix, fractions, signs and polynomials
printed in the paper with their output. The general statements are proved in the paper, not by these programs.

## Use of AI

The proofs and the text were produced with AI systems (GPT-6.1 Sol, with editing by Claude Opus 5.5) under the
author's direction. They were checked by independent reviews with AI models (GPT-6.1 Sol and Gemini 4 Argon) and by
the exact computations in [`anc/`](anc/). No human expert has reviewed the paper. The author takes responsibility for
the content.

## Citation

```bibtex
@misc{Guo2026ConcyclicRamsey,
  author = {Guo, Jizhou},
  title = {Concyclic {E}uclidean {R}amsey sets with three-dimensional moduli},
  year = {2026},
  month = oct,
  note = {23 October 2026}
}
```
