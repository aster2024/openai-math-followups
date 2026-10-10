# Liouville signs at almost-prime pairs: a reduction to one inequality and two model sequences

Jizhou Guo — mitsuha2021b@gmail.com — 10 October 2026

[**Paper (PDF, 36 pages)**](paper.pdf) · [LaTeX source](source/)

The paper [`rough-pairs-fixed-distance/`](../rough-pairs-fixed-distance/) counts each sign pattern of
(λ(n), λ(n + h)) on integers n ≤ X with n and n + h free of prime factors up to exp((log X)^(1/3750)). This paper
asks what is needed for a bounded number of prime factors.

## The reduction

Let λ be the Liouville function, h ≥ 2 a fixed even integer and c > 0 fixed. Put σ = c/log X and

```math
J_\sigma(n)=\prod_{p\mid n}\bigl(1-p^{-\sigma}\bigr),\qquad W_X(n)=J_\sigma(n)\,J_\sigma(n+h),\qquad M_0=\sum_{n\le X}W_X(n).
```

**Theorem 1.1.** M₀ has order X/(log X)². The integers n ≤ X with Ω(n) > K or Ω(n + h) > K carry at most
C′·u^(−K)·X/(log X)² of this mass, with u = 2^(1/1000). For every 0 < ε ≤ 1/4 there is c₀(ε) such that, for fixed
c ≥ c₀(ε) and all large X,

```math
\Bigl|\sum_{n\le X}\lambda(n)W_X(n)\Bigr|+\Bigl|\sum_{n\le X}\lambda(n+h)W_X(n)\Bigr|\le\varepsilon M_0 .
```

**Theorem 1.2.** Suppose in addition that, for all large X,

```math
\Bigl|\sum_{n\le X}\lambda(n)\,\lambda(n+h)\,W_X(n)\Bigr|\le(1-2\varepsilon)\,M_0 .
```

Then there is a fixed K such that each of the four sign patterns of (λ(n), λ(n + h)) occurs for ≫ X/(log X)²
integers n ≤ X with Ω(n) ≤ K and Ω(n + h) ≤ K.

The paper does not prove this inequality. Theorem 1.1 and the deduction use classical inputs only: the
Nair–Tenenbaum bound in Henriot's form, the fundamental lemma of the sieve and the Bombieri–Vinogradov theorem for
λ in all residue classes.

**Proposition 1.3.** The same conclusion follows from a bound C·X/(log X)², with a finite C, for the sieve
remainder

```math
\sum_{d\le X^{\theta}}\mu^2(d)\sum_{r(r+h)\equiv0\ (d)}\Bigl|\sum_{\substack{n\le X\\ n\equiv r\ (d)}}\lambda(n)\lambda(n+h)\Bigr|
```

at one fixed level θ > 0. A bound of this form at level exp((log X)^α), 0 < α < 1, gives the sign patterns with
Ω(n), Ω(n + h) ≤ s₀·(log X)^(1−α) + O(1), a bound that grows with X.

## Two model sequences

**Theorem 1.4.** There is a sequence f : ℕ → {±1} such that

- sums of f over intervals and arithmetic progressions, with additive twists, have square-root cancellation up to
  a factor √log; likewise twists by Dirichlet characters of modulus and height at most a fixed power, the
  two-point sums of f at fixed non-proportional affine pairs, at all shifts, and the reflected sums Σ f(n)f(N − n);
- the average over all residue classes Σ_{d ≤ X^θ} d⁻¹ Σ_{r mod d} |Σ_{n ≤ X, n ≡ r (d)} f(n)f(n + 2)| is
  ≪ X·exp(−log X/(4 log log X));
- the sieve remainder of the pair (n, n + 2) at every level up to exp((log X)^α), α < 1 fixed, is at most
  X^(1/2+o(1));
- and yet, for every fixed 0 < θ < 1, the sieve remainder at level X^θ satisfies

```math
\sum_{d\le X^{\theta}}\mu^2(d)\sum_{r(r+2)\equiv0\ (d)}\Bigl|\sum_{\substack{n\le X\\ n\equiv r\ (d)}}f(n)f(n+2)\Bigr|\ \sim\ \frac{c_2\log2}{32}\,\theta^2\,X\log X,
\qquad c_2=\frac38\prod_{p>2}\Bigl(1+\frac2p\Bigr)\Bigl(1-\frac1p\Bigr)^2 .
```

**Theorem 1.5.** For every fixed non-zero integer h there is a sequence f : ℕ → {±1} with bounds
≪ Y^(3/4)·√log Y for all one-point and two-point sums along affine forms with coefficients up to Y, with bounds
for Dirichlet characters of polynomial modulus and for Type I sums, for which the matrices
(f(mℓ + h)) on (T_j, 2T_j] × (3T_j, 6T_j] have operator norm at least c_h·T_j/log T_j along a sequence T_j → ∞.
One sequence does this for h = 1 and h = 2 on alternating scales.

An argument that uses only the listed estimates, together with identities and inequalities valid for arbitrary
bounded sequences, applies equally to these sequences, for which the sieve remainder bound of Proposition 1.3,
respectively the Type II bound, fails. A proof of those bounds for λ therefore has to use further information
or stronger estimates than those listed. The sequences are not completely multiplicative; complete multiplicativity, the values at the primes,
Euler products, zero-free regions and higher-order correlations are not among the listed estimates. The
constructions do not bear on whether the inequality of Theorem 1.2 holds.

## Two further statements

**Theorem 1.6.** An exact substitution U(x)V(y) + h = R(x)S(y)(xy + h) on a product set, with separate maps U, V
and non-zero rational weights R, S, has U and V given by Möbius transformations. If its values are integers of
size at most X^C and it does not preserve products, one of its sides has at most K·X^η elements; hence covering a
proportion ρ of an r × s set of integer points needs at least ρ·min(r, s)/(K·X^η) such pieces.

**Theorem 1.7.** For a class of non-negative divisor weights defined in the paper (weights depending only on the
divisor, the independent divisibility law, 0/1 retention, one bin per retained edge), the second-moment
normalisation at an individual root modulo v forces v ≤ exp(O(L)) when the weight is supported on integers
composed of primes up to e^L. Signed weights and cancellation between roots are outside the class.

## What the proofs use

- The reduction: classical inputs, as above. Two auxiliary statements (a remark on one-point asymptotics and a
  proposition on a short Type I sum) are relative to the zero-free half-plane Re s > 7/8 of the
  [OpenAI mathematics release](https://github.com/openai/math) (family 003), pinned to commit
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`; nothing else in the paper uses it.
- The two sequences: random signs with planted correlations, the bounded-differences inequality and the
  Borel–Cantelli lemma, so that one realisation satisfies all the listed bounds at all large scales.
- Theorem 1.6: elementary algebra. Theorem 1.7: an entropy bound for the divisor selected by the weight.

## Related work

- Sequences satisfying sieve hypotheses and vanishing on the primes: Selberg's examples and Bombieri's
  asymptotic sieve. Ford and Maynard ([arXiv:2407.14368](https://arxiv.org/abs/2407.14368)) give a general
  procedure for constructing non-negative sequences satisfying prescribed Type I and Type II estimates, and show
  that a substantial Type II range is always necessary for a non-trivial lower bound for the sum over primes.
- Friedlander and Iwaniec (Ann. of Math. 148 (1998)): an additional axiom in the sieve which breaks the parity
  problem.
- Tao ([blog post, 21 November 2014](https://terrytao.wordpress.com/2014/11/21/a-general-parity-problem-obstruction/)):
  a parity obstruction for properties defined by sign patterns of λ, presuming a pseudorandomness conjecture.
- Deligiannis ([doi:10.5281/zenodo.21581938](https://doi.org/10.5281/zenodo.21581938)): a lower bound for the
  number of Goldbach representations deduced from two cancellation hypotheses for sifted two-point Liouville sums;
  and ([doi:10.5281/zenodo.19504780](https://doi.org/10.5281/zenodo.19504780)) an analysis of limitations of
  existing methods for such cancellation. Arneth
  ([doi:10.5281/zenodo.23011047](https://doi.org/10.5281/zenodo.23011047)): a sifted fixed-shift Liouville
  cancellation formulated as the remaining analytic problem of a programme on the binary Goldbach problem.
- Goldston, Graham, Pintz and Yıldırım ([arXiv:0803.2636](https://arxiv.org/abs/0803.2636)); Matomäki, Radziwiłł
  and Tao ([arXiv:1509.01545](https://arxiv.org/abs/1509.01545)).

## Files

Read [paper.pdf](paper.pdf). To compile the source, with Tectonic installed,

    cd source
    tectonic main.tex

or, with the included bibliography file `main.bbl`, run `pdflatex main.tex` twice. `SHA256SUMS` lists the
checksums of the files in this directory.

## Citation

```bibtex
@misc{Guo2026AlmostPrimePairsReduction,
  author = {Guo, Jizhou},
  title = {Liouville signs at almost-prime pairs: a reduction to one inequality and two model sequences},
  year = {2026},
  month = oct,
  howpublished = {\url{https://github.com/aster2024/openai-math-followups/tree/main/almost-prime-pairs-reduction}},
  note = {Preprint, 10 October 2026}
}
```
