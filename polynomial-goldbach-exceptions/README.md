# Exceptional sets for sums and differences of two primes along polynomial sequences

Jizhou Guo — mitsuha2021b@gmail.com — 29 October 2026

[**Paper (PDF, 15 pages)**](paper.pdf) · [LaTeX source](source/) · [Ancillary checks](anc/)

## Result

Let Q be a fixed integer polynomial of degree d = 2 or 3 with positive leading
coefficient. Count positive integer parameters m ≤ N for which Q(m) is positive
and even but is not a sum of two primes. Relative to the analytic inputs below,
the paper proves

```math
E_+(N;Q)\ll_{Q,\varepsilon}N^{d/4+\varepsilon}.
```

The exponents are 1/2 for quadratics and 3/4 for cubics. The same bound holds for
failure of a representation Q(m) = p₂ − p₁ with both primes at most C_Q N^d, where

```math
C_Q=2\left(1+\sum_{j=0}^d|[t^j]Q|\right).
```

The Pintz–Maynard–Pandey–Radziwiłł alternative gives N^(7d/24+ε), hence the
parameter exponents 7/12 and 7/8. Primes may repeat.

For a degree-two integer polynomial mapping an entire interval I of consecutive
integers into [X/2, X], the number of even-valued exceptional parameters is
O_ε(X^(1/4+ε)), with alternative bound O_ε(X^(7/24+ε)), independently of the
coefficients, the location of I and its length. The difference version has both
primes at most 2X.

The argument is the classical thin-set exceptional-set mechanism, with the
exponential sum taken over the exceptions themselves. For doubled squares, the
Pintz–MPR route is the argument of [Perelli–Pintz, (3.1)–(3.10)](https://arxiv.org/abs/2610.29470v1)
with that sum restricted to the exceptions, which changes N^(19/24+ε) to
N^(7/12+ε); the exponent 1/2 uses Li–Liu's fourth moment.
The paper gives the quadratic and cubic multiplicity proofs, treats both cubic
V = 0 branches, and exhibits an even-valued moving cubic family for which the
uniform multiplicity extension fails.

## Inputs

The paper's prime-distribution conclusions are relative to these explicitly
stated theorems and hypotheses; Section 2 gives their full interfaces.

- [Li–Liu, arXiv:2610.26756v1](https://arxiv.org/abs/2610.26756v1), Theorem 1 and
  Proposition 4.1: the minor-arc fourth moment and matching major coefficients
  for sums and differences, under a common fixed Dirichlet zero-free boundary
  Θ < 11/12. At Θ = 7/8 the proof of Li–Liu's Theorem 1 admits, for example,
  κ = 899/2000; this choice is not needed for the results.
- [Pintz's major-arc formula, arXiv:1804.05561v1](https://arxiv.org/abs/1804.05561v1),
  Theorem 1, (2.10)–(2.11), and
  [Maynard–Pandey–Radziwiłł, arXiv:2608.14777v1](https://arxiv.org/abs/2608.14777v1),
  Theorem 1.1, for the alternative under any common fixed boundary Θ < 1.
- [OpenAI, *The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8*](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf),
  Theorem 1.1, supplies the common zero-free hypothesis for every Dirichlet
  L-function, with the principal pole allowed. All OpenAI references are pinned
  to commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`; the
  [family 003 scope document](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/docs/003.md)
  specifies the Lean statement.

## Related work

[Perelli (1996), Theorem 1 and Corollary 1](https://doi.org/10.4171/rmi/205)
treat fixed general polynomials and parameter short intervals with arbitrary
logarithmic savings.
[Brüdern–Kawada–Wooley (2000), Theorem 1](https://doi.org/10.1112/S002557930001576X)
give N^(1−c/d) for a fixed degree-d polynomial; their proof averages the
minor-arc contribution against a sign-weighted exponential sum over all
parameters.
[Pintz (2021), Theorem 5, attributed there to Perelli and Pintz](https://real.mtak.hu/124681/1/Cikk2020Rivista.pdf)
states, unconditionally, E₂(N) ≪ N^(4/5+ε) for doubled squares.
[Perelli–Pintz, arXiv:2610.29470v1, Theorem 1](https://arxiv.org/abs/2610.29470v1)
states E₂(N) ≪ N^(19/24+ε); N is the parameter cutoff in 2m².
[Pintz–Althöfer, Theorem 1](https://arxiv.org/abs/2610.15559v1) obtain the
ordinary-integer Goldbach bound X^(7/12+ε) under a common fixed zero-free
half-plane. Li–Liu's Theorem 2 gives the ordinary-integer square-root bound for
both signs from their fourth-moment theorem.

Later work lowers the zero-free boundary below 7/8, including the
[QRH tracker entry with Dirichlet boundary 0.8739558](https://github.com/GTimG/QuasiRiemannTracker/pull/86).
Such improvements leave the exponents in the two routes here unchanged:
Li–Liu's choice uses max(Θ, 7/8), while the alternative's power 7/24 comes from
the 19/24 term in MPR's estimate.

## Files

| Path | Content |
| --- | --- |
| `paper.pdf` | The paper |
| `source/main.tex`, `source/main.bbl`, `source/references.bib` | LaTeX source and bibliography |
| `anc/` | Exact finite checks and their results |
| `SHA256SUMS` | Checksums of the distributed files |

## Build

With Tectonic installed, compile from the source directory:

```sh
cd source
tectonic --untrusted --keep-logs --keep-intermediates main.tex
cp main.pdf ../paper.pdf
```

From the root of this paper directory, run the finite checks:

```sh
python3 anc/run_all.py
```

See [anc/README.md](anc/README.md) for dependencies, the one-line summaries and
the scope of the checks.

## Use of AI

The proofs and the text were produced with AI systems (GPT-6.1 Sol, GPT-6 Astra
and Claude Opus 5.5) under the author's direction, checked by independent reviews
with AI models and by the computations in the ancillary files. No human expert
has reviewed them. The author takes responsibility for the content.
