# Goldbach-type representations with prescribed Liouville signs

Jizhou Guo — mitsuha2021b@gmail.com — 8 October 2026

[**Paper (PDF, 28 pages)**](paper.pdf) · [LaTeX source](source/) · [Lean ancillary files](anc/)

## Result

Let λ be the Liouville function. For every sufficiently large integer N, each of the four ordered sign patterns
(λ(a), λ(b)), with a, b ≥ 1 and a + b = N, occurs

```math
\frac{N}{4}+O\left(\frac{N}{(\log N)^{c}}\right),\qquad c=10^{-200},
```

times. Equivalently,

```math
\sum_{1\le n\lt N}\lambda(n)\,\lambda(N-n)=O\left(\frac{N}{(\log N)^{c}}\right).
```

This proves, for the Liouville function, the conjecture of Corrádi and Kátai that the sum is o(N), in the form
stated in Mangerel (IMRN 2024, §1.1) and Krishnamoorthy (arXiv:2608.13266, Conjecture 1).

Part II inserts the zero-free half-plane Re s > 7/8 for Dirichlet L-functions into results of Pintz,
Chen–Gupta–Li, Montgomery–Vaughan and Martin:

- Pintz's conditional exponent 3/5 for the exceptional set in the binary Goldbach problem holds unconditionally;
- the least prime in a reduced residue class modulo q is O(q^(7/3+ε)) for every ε > 0;
- the least non-residue of a non-principal character modulo q is O((log q)^8);
- the least primitive root and the least prime primitive root modulo p are O((log p)^24).

## What the proof uses

The [OpenAI library](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean), pinned to
commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`:

- Family 003: `OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re` — every Dirichlet L-function is
  zero-free in Re s > 7/8 (principal pole excluded).
- Family 007 (two-point correlations): the closed-word column bound, the finite residue and affine-word
  comparisons, the positive deletion and prohibited-row comparisons, the prohibited-site probability bound, the
  full-pool padding cost, and the noncommuting spectral transfer. Sections 3–4 of the paper transcribe the named
  declarations with their quantifier orders.

Published analysis: Matomäki–Radziwiłł–Tao; Klurman–Mangerel–Teräväinen (arXiv:1909.12280v5); and, for Part II, Pintz,
Chen–Gupta–Li (preprint), Bach, Montgomery–Vaughan and Martin.

B. Sandlund's research memo of 7 October 2026
([brycesandlund/quasi-riemann-algorithms](https://github.com/brycesandlund/quasi-riemann-algorithms)) also derives
proper-subgroup bounds and least prime primitive-root bounds from a fixed Dirichlet zero-free half-plane.

The inputs printed in the paper are mathematical transcriptions of compiled Lean declarations. The reflected
asymptotic, the bound on the comparison exponent (at most 10^6), the resulting value of c, and the classical
deductions of Part II are written mathematics. The ancillary Lean files read back the types and axioms of the
inputs and prove the finite CRT, matrix and degree lemmas used in the paper; see [`anc/README.md`](anc/README.md)
for the toolchain and how to check them.

## Files

| Path | Content |
|---|---|
| `paper.pdf` | The paper |
| `source/main.tex`, `source/main.bbl`, `source/references.bib` | LaTeX source (pdfLaTeX or Tectonic) |
| `anc/CRTTransport.lean` | Transport of the prohibited predicates under scaling and CRT |
| `anc/TwoLayerRows.lean` | Weighted square bound for the two-layer lift |
| `anc/ExplicitBudget.lean` | Degree exponents 8457 and 8458 |
| `anc/Interfaces.lean`, `anc/InputStatements.lean` | Types and axioms of the input declarations |
| `SHA256SUMS` | Checksums of the files above |

## Citation

```bibtex
@misc{Guo2026LiouvilleSigns,
  author = {Guo, Jizhou},
  title = {Goldbach-type representations with prescribed {L}iouville signs},
  year = {2026},
  month = oct,
  howpublished = {\url{https://github.com/aster2024/openai-math-followups/tree/main/liouville-goldbach}},
  note = {Preprint, 8 October 2026}
}
```
