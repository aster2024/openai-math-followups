# Follow-ups to the OpenAI mathematics release

Notes and papers by Jizhou Guo (mitsuha2021b@gmail.com) that build on results of the
[OpenAI mathematics release](https://github.com/openai/math) of October 2026, pinned throughout to commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

## Contents

### [`almost-prime-pairs-reduction/`](almost-prime-pairs-reduction/) — Liouville signs at almost-prime pairs: a reduction to one inequality and two model sequences

Paper (36 pages), 10 October 2026: [PDF](almost-prime-pairs-reduction/paper.pdf).

Let h ≥ 2 be a fixed even integer, σ = c/log X, J_σ(n) = ∏_{p | n} (1 − p^(−σ)) and W(n) = J_σ(n)·J_σ(n + h). The sum
M₀ = Σ_{n ≤ X} W(n) has order X/(log X)², and for 0 < ε ≤ 1/4 and fixed c ≥ c₀(ε) the absolute values of the sums of
λ(n)W(n) and of λ(n + h)W(n) add up to at most εM₀ for all large X. Consequently the single inequality

```math
\Bigl|\sum_{n\le X}\lambda(n)\,\lambda(n+h)\,W(n)\Bigr|\le(1-2\varepsilon)\,M_0\qquad\text{for all large }X
```

would give, for a fixed K, ≫ X/(log X)² integers n ≤ X with Ω(n), Ω(n + h) ≤ K for each sign pattern of
(λ(n), λ(n + h)). The paper does not prove this inequality; this part uses classical inputs only.

The paper also constructs two ±1-valued sequences. The first has square-root bounds, up to a factor √log X, on
intervals, progressions, additive and character twists, fixed non-proportional positive-slope two-point sums,
all-shift sums and reflected sums, and for every fixed 0 < θ < 1 its sieve remainder for the pair (n, n + 2) at
level X^θ is asymptotic to (c₂·log 2/32)·θ²·X·log X. The second has bounds ≪ Y^(3/4)·√log Y for one-point sums and
for two-point sums along pairs of distinct affine forms, bounds for characters of polynomial modulus and for
Type I sums, and its matrices (f(mℓ + h)) have operator norm ≫ √(MN)/log X on infinitely many balanced rectangles.
Arguments that use only the listed estimates apply equally to these sequences, so a proof for λ of a bound
C·X/(log X)² for the sieve remainder at a fixed level X^θ, or of the operator-norm bound √(MN)·(log X)^(−3/2−κ), has
to use further information or stronger estimates than those listed. These constructions do not bear on whether
the inequality above holds. The paper further classifies exact separated-variable substitutions and
proves a bound for a class of non-negative divisor weights.

### [`cm-elliptic-curves/`](cm-elliptic-curves/) — A zero-free half-plane for Hecke L-functions of nonzero angular type and for the curves y² = x³ + D

Paper (36 pages), 8 October 2026: [PDF](cm-elliptic-curves/paper.pdf). Programs checking the explicit identities are in [`cm-elliptic-curves/anc/`](cm-elliptic-curves/anc/).

Let K = Q(√−3). Every unitary Hecke character η of K of finite conductor and non-zero angular type (such
characters have infinite order) satisfies L_K(s, η) ≠ 0 for Re s > 11/12, with the same half-plane for every conductor
and every angular type. Consequently, for every non-zero rational D the elliptic curve E_D : y² = x³ + D satisfies

```math
L(E_D,s)\neq 0\qquad\text{for }\ \mathrm{Re}\,s\gt \frac{17}{12},
```

so that the non-trivial zeros of L(E_D, s) lie in 7/12 ≤ Re s ≤ 17/12. The paper also gives the distribution of
Eisenstein primes in sectors and the Sato–Tate distribution of E_D with error term O(x^(11/12+ε)), a bound
(log N(E_D))^A, for every A > 12, for the least good prime at which a_p(E_D) lies in a prescribed range, and zero-free
half-planes for all symmetric powers of E_D and for all newforms with complex multiplication by K.

The two zero-free statements above, and those for CM newforms and symmetric powers, are also stated in an earlier
note of B. Yates ([Zenodo, 7 October 2026](https://doi.org/10.5281/zenodo.23207672)), conditional on the correctness
of OpenAI's 11/12 argument and with the same raising of the cusp-derivative order; this paper was prepared
independently of it. The distribution estimates and the least-prime bound are not in that note.

The proof extends the cubic-theta method of OpenAI's paper
[The Quasi-Riemann Hypothesis](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-October-5-2026)
(5 October 2026) from finite-order characters to characters of non-zero angular type: the higher angular modes are
obtained from pure Wirtinger derivatives of the cubic theta function at the cusps.

### [`cm-elliptic-curves-gaussian/`](cm-elliptic-curves-gaussian/) — A zero-free half-plane for angular Hecke L-functions over Q(i) and for the curves y² = x³ − Dx

Paper (35 pages), 24 October 2026: [PDF](cm-elliptic-curves-gaussian/paper.pdf). Programs checking the explicit identities are in [`cm-elliptic-curves-gaussian/anc/`](cm-elliptic-curves-gaussian/anc/).

Let K = Q(i). Every unitary Hecke character η of K of finite conductor and non-zero angular type satisfies
L_K(s, η) ≠ 0 for Re s > 11/12, with the same half-plane for every conductor, every angular type and every norm
phase. Consequently, for every non-zero rational D the elliptic curve E_D : y² = x³ − Dx, in particular every
congruent number curve y² = x³ − n²x, satisfies

```math
L(E_D,s)\neq 0\qquad\text{for }\ \mathrm{Re}\,s\gt \frac{17}{12}.
```

The paper also gives the distribution of Gaussian primes in sectors and of the traces a_p(E_D) with error term
O(x^(11/12+ε)), and zero-free half-planes for all symmetric powers of E_D and for all newforms attached to Hecke
characters of K. The proof passes by quadratic base change to Q(ζ₁₂) and adapts the cubic-theta method of OpenAI's
11/12 paper there, using the Kazhdan–Patterson cubic theta function over Q(ζ₁₂) and Poisson summation over complete
orbits of S-units.

### [`concyclic-ramsey-moduli/`](concyclic-ramsey-moduli/) — Concyclic Euclidean Ramsey sets with three-dimensional moduli

Paper (17 pages), 23 October 2026: [PDF](concyclic-ramsey-moduli/paper.pdf). Exact-arithmetic checks are in [`concyclic-ramsey-moduli/anc/`](concyclic-ramsey-moduli/anc/).

Let A be a set of n ≥ 7 distinct points on a circle, and let M(A) be the field generated over Q by its four-point
cross ratios. If trdeg_Q M(A) = 3, then A is Euclidean Ramsey if and only if its points split into two groups of at
least three points each, such that all four-point cross ratios inside each group are algebraic. For seven points this
says that A is Ramsey if and only if some four-point cross ratio is algebraic. Consequently, for x, y, z algebraically
independent, the seven circle points with stereographic parameters −2, 0, 2, x, y, −4 − x − 2y, z are not Ramsey; this
is the family left open in Appendix E of D. Pálvölgyi's
[A cyclic non-Ramsey heptagon](https://arxiv.org/abs/2609.23327v1).

The "if" direction applies the sufficient direction of Theorem 1.1 of OpenAI's paper
[A classification of finite Euclidean Ramsey configurations](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-classification-of-finite-Euclidean-Ramsey-configurations-September-23-2026/paper.pdf)
(23 September 2026) and is a circle case of W. Strinz's two-group theorem
([spherical-ramsey v1.1.0](https://doi.org/10.5281/zenodo.23396387)). The "only if" direction and the non-Ramsey
example use neither direction of OpenAI's theorem: the paper includes a self-contained proof of the necessity of the
tensor condition and derives the classification from a second-order expansion of the tensor equations along the
derivations of M(A). An explicit Ramsey family on the curve y² = x³ − 2, with moduli of transcendence degree one and
no algebraic cross ratio, shows that the dimension hypothesis cannot simply be dropped.

### [`explicit-class-numbers/`](explicit-class-numbers/) — Explicit Littlewood-type bounds for L(1,χ) and class numbers from a zero-free half-plane

Paper (13 pages), 28 October 2026: [PDF](explicit-class-numbers/paper.pdf). Programs evaluating the constants and checking the bounds numerically are in [`explicit-class-numbers/anc/`](explicit-class-numbers/anc/).

Let 1/2 ≤ θ < 1 and let χ be a nonprincipal Dirichlet character modulo q ≥ 3 whose L-function has no zeros with
Re s > θ. The paper gives two-sided bounds for |L(1,χ)| of Littlewood's shape (M + log log q)^(±1), with every
constant explicit in θ. For θ = 7/8, the half-plane of OpenAI's paper
[The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf)
(30 September 2026), this gives 1/(10.41 (10 + log log q)) ≤ |L(1,χ)| ≤ 17.12 (10 + log log q) and, for every
fundamental discriminant −d < 0,

```math
h(-d)\ \ge\ rac{\sqrt d}{32.69\,(10+\log\log d)},
```

so that h(−d) > 100 for d ≥ 1.83·10⁹ and h(−d) > 1000 for d ≥ 1.88·10¹¹. The statements hold unconditionally exactly
when the input theorem is correct. Friedlander (1977) records that Littlewood's GRH argument extends to a zero-free
half-plane, and OpenAI's paper of 5 October 2026 and K. Kimura
([arXiv:2610.21511v2](https://arxiv.org/abs/2610.21511v2), which determines all imaginary quadratic fields with class
number at most 2000 from the release's exclusion of Landau–Siegel zeros) note the resulting bound
h(−d) ≫ √d/log log d with an effective constant; the paper works out explicit constants and compares the thresholds
with those of Watkins and Kimura.

### [`explicit-cubic-nonresidues/`](explicit-cubic-nonresidues/) — Explicit least prime ideals and cubic non-residues over Q(√−3) from a zero-free half-plane

Paper (19 pages), 28 October 2026: [PDF](explicit-cubic-nonresidues/paper.pdf). Programs checking the constants and the analytic lemmas numerically are in [`explicit-cubic-nonresidues/anc/`](explicit-cubic-nonresidues/anc/).

Let F = Q(√−3). Taking as a hypothesis the statement of Theorem 1.1 of OpenAI's paper
[The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf)
for finite-order Hecke L-functions of F, the paper gives fully explicit bounds of norm (C log N(m) + C′)^8 for the
least prime ideal outside a proper subgroup of a ray class group modulo m, for the least cubic non-residue modulo a
prime ideal, and for the least prime ideal in each ray class (with a factor h_m^8, which cannot be replaced by a power
of log N(m)). For every integer a that is not a perfect cube it gives a prime p ≡ 1 (mod 3) modulo which a is not a
cubic residue, with

```math
p\ <\ (72\log|a|+297.76)^8\ \le\ (502\log|a|)^8 ;
```

here the character p ↦ (a/p)₃ is a ray class character of F, so the half-plane for Dirichlet L-functions alone does
not suffice. The shape of the bounds and the exponent 1/(1 − 7/8) = 8 are those of Bach (1982, 1990); B. Hu's
[preprint](https://hexagonmath.org/2610.00216v1) states an effective Chebotarev bound with exponent 8 over every number
field with an unspecified constant. The paper works out explicit constants over Q(√−3).

### [`hot-spots-convex-planar/`](hot-spots-convex-planar/) — First Neumann eigenfunctions of convex planar domains attain their extrema on the boundary

Paper (32 pages), 10 October 2026: [PDF](hot-spots-convex-planar/paper.pdf).

Let D be a bounded convex planar domain, with no smoothness assumption on its boundary, and u a non-zero
eigenfunction for its first positive Neumann eigenvalue. Then

```math
\max_{\overline D}u=\max_{\partial D}u,\qquad \min_{\overline D}u=\min_{\partial D}u,
```

u has no strict or isolated local extremum in D, and every isolated critical point of u in D has index zero. This
holds for every member of the eigenspace, also when the eigenvalue is double.

These statements are deduced from OpenAI's paper
[Strict hot spots and absence of interior critical points on smooth simply connected planar domains](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Strict-hot-spots-and-absence-of-interior-critical-points-on-smooth-simply-connected-planar-domains-September-24-2026/main.pdf)
(24 September 2026), whose theorem is for bounded simply connected planar domains with C^∞ boundary. For a simple eigenvalue the deduction is an
approximation argument. For a double eigenvalue each member of the eigenspace is obtained as a limit of first
eigenfunctions of smooth domains that need not be convex. Independently of that paper, the first positive Neumann
eigenvalue of every bounded convex planar domain has multiplicity at most two, and the nodal set of each
eigenfunction is a single arc joining two distinct boundary points.

### [`liouville-goldbach/`](liouville-goldbach/) — Goldbach-type representations with prescribed Liouville signs

Paper (28 pages), 8 October 2026: [PDF](liouville-goldbach/paper.pdf). Lean 4 formalization of the main theorem (with the
exponent c = 10⁻²⁰⁰), conditional on one published estimate: [`liouville-goldbach/lean/`](liouville-goldbach/lean/).

Let λ be the Liouville function. For every sufficiently large integer N, each of the four sign patterns
(λ(a), λ(b)) with a + b = N occurs N/4 + O(N (log N)^(−c)) times. Equivalently,

```math
\sum_{1\le n\lt N}\lambda(n)\,\lambda(N-n)=O\left(\frac{N}{(\log N)^{c}}\right),
```

which proves the conjecture of Corrádi and Kátai for the Liouville function.

Part II gives consequences of the zero-free half-plane Re s > 7/8 for Dirichlet L-functions: the exceptional set
in the binary Goldbach problem, the least prime in an arithmetic progression, least non-residues, and least
primitive roots. For the exceptional set, later preprints give the exponent 7/12 from the same half-plane
(J. Pintz and I. Althöfer, [arXiv:2610.15559](https://arxiv.org/abs/2610.15559)) and the bound N^(1/2)(log N)^100
assuming that all zeros of primitive Dirichlet L-functions have real part at most a fixed Θ < 11/12 (H. Li and Z. Liu,
[arXiv:2610.26756](https://arxiv.org/abs/2610.26756)).

### [`mobius-goldbach-shift/`](mobius-goldbach-shift/) — The Möbius function at N − p

Paper (65 pages), version 2 of 23 October 2026 (version 1: 22 October 2026): [PDF](mobius-goldbach-shift/paper.pdf). Programs checking finite instances of the algebraic identities are in [`mobius-goldbach-shift/anc/`](mobius-goldbach-shift/anc/).

The statements are conditional on the arguments of G. Lü, Z. Wang and J. Wu
([arXiv:2610.20242v1](https://arxiv.org/abs/2610.20242v1)), which state that Σ_{p≤x} μ(p + 2) = o(π(x)): the paper
assumes that the arguments of their Sections 4.2–4.7 and Appendix A are correct as written. Under this assumption and
the zero-free half-plane Re s > 7/8 for Dirichlet L-functions, as N → ∞ through even integers,

```math
\sum_{p<N}\mu(N-p)=o(\pi(N)),\qquad \#\{p<N:\ \mu(N-p)=\pm1\}=\Bigl(\frac{A_N}{2}+o(1)\Bigr)\pi(N),\qquad A_N=\prod_{p\nmid N}\Bigl(1-\frac{1}{p(p-1)}\Bigr).
```

For even N with rad(N) ≤ (log N)^C the same holds with Iwaniec's zero-free region of 1974 and Burgess's bound in place
of the half-plane. Assuming in addition the remaining arguments of Lü, Wang and Wu as written, the paper gives the
corresponding statements for μ(p + h), uniformly for 0 < |h| ≤ (log x)^C, and Liouville versions with sign densities
1/2 + o(1). The paper adapts their determinant method to the shift N and lists every change by section, equation and
page.

Version 2 adds, under the same assumption on Lü, Wang and Wu and the half-plane Re s > 7/8, the bound
Σ_{p≤x, εp+h≥1} f(εp + h) = O(π(x)/√(log log x)) for f = μ and f = λ, uniformly for ε = ±1 and 0 < |h| ≤ x(log x)^C
(which contains the statement for N − p), together with versions for primes in progressions to moduli
q ≤ (log x)^C, for values εp + h (h even) without prime factors up to exp((log x)^a), any fixed a < 1/2, and two
conditions on the radical of N (one with a uniform real-zero gap, one with avoidance of a possible Landau–Page
exceptional conductor) under which the reflected statements hold without the half-plane.

### [`rough-goldbach-parity/`](rough-goldbach-parity/) — Sums of two rough numbers with prescribed Liouville signs

Paper (23 pages), 9 October 2026: [PDF](rough-goldbach-parity/paper.pdf). Programs checking finite instances of the algebraic identities are in [`rough-goldbach-parity/anc/`](rough-goldbach-parity/anc/).

Let λ be the Liouville function and P⁻(n) the least prime factor of n. For every sufficiently large even integer N
and each pair of signs (σ, τ),

```math
\#\{\,n:\ N/3\le n\le 2N/3,\ \ P^-(n)\gt z,\ \ P^-(N-n)\gt z,\ \ \lambda(n)=\sigma,\ \ \lambda(N-n)=\tau\,\}\ \ge\ c\,\frac{N}{(\log N)^{1/4}},
\qquad z=\exp\bigl((\log N)^{1/10}\bigr),
```

and n, N − n may also be taken squarefree with at most ⌈2 log log N⌉ prime factors.

The proof combines the zero-free half-plane Re s > 7/8 for Dirichlet L-functions with the weighted dilation graphs
of OpenAI's paper
[Weighted dilation graphs, smooth shifted primes and totient fibers](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Weighted-Dilation-Graphs-Smooth-Shifted-Primes-and-Totient-Fibers-September-24-2026/paper.pdf)
(24 September 2026). Two of the graph estimates are needed for displacements that are multiples of N and for prime
groups with the prime factors of N removed; the paper obtains these from the proofs given there, going through
every place where the displacement and the interval structure of the groups enter.

### [`rough-pairs-fixed-distance/`](rough-pairs-fixed-distance/) — Rough numbers at a fixed distance with prescribed Liouville signs

Paper (38 pages), 10 October 2026: [PDF](rough-pairs-fixed-distance/paper.pdf). Programs checking finite instances of the algebraic identities are in [`rough-pairs-fixed-distance/anc/`](rough-pairs-fixed-distance/anc/).

Let h ≥ 2 be a fixed even integer. Uniformly for 2 ≤ z ≤ exp((log X)^(1/3750)), each of the four sign patterns of
(λ(n), λ(n + h)) occurs for

```math
\tfrac14\,X\,V_h(z)\,\bigl(1+O_h((\log X)^{-\gamma})\bigr),\qquad V_h(z)=\prod_{p\le z}\Bigl(1-\frac{\nu_h(p)}{p}\Bigr),
```

integers n ≤ X such that n and n + h have no prime factor up to z (ν_h(p) = 1 if p divides h, and 2 otherwise).
Consequently each pattern occurs for ≫ X/(log X)^(1/1875) integers n ≤ X with n and n + h squarefree, free of prime
factors up to exp((log X)^(1/3750)), and with at most (1 − 1/4000)·log log X prime factors. The paper also treats a
weight on the small prime factors and a weight on all prime factors.

The proofs adapt the graph argument of OpenAI's paper proving the two-point Chowla conjecture (family 007 of the
release). The operator of that paper is changed so that the sieve density stays inside it, and the paper proves the
estimates it needs for the changed operator by going through the proofs given there. The zero-free half-plane
Re s > 7/8 is not used.

### [`shifted-prime-parity/`](shifted-prime-parity/) — Shifted primes with a prescribed parity of the number of prime factors

Paper (31 pages), 9 October 2026: [PDF](shifted-prime-parity/paper.pdf). Programs checking the algebraic identities on finite ranges are in [`shifted-prime-parity/anc/`](shifted-prime-parity/anc/).

Let λ be the Liouville function. For every X ≥ X\*, every integer h with 0 < |h| ≤ (log X)⁵ and each sign s,

```math
\#\{p\le X\ \text{prime}:\ p+h\gt 0,\ p+h\ \text{squarefree},\ \lambda(p+h)=s\}\ \ge\ c\,\frac{X}{(\log X)^{300}} .
```

Consequently, for every non-zero integer h, the number of prime factors of p + h is even for infinitely many primes p
and odd for infinitely many primes p; for h = 2 this gives both parities of the number of prime factors of p + 2.
Later, G. Lü, Z. Wang and J. Wu ([arXiv:2610.20242](https://arxiv.org/abs/2610.20242), 14 October 2026) stated that
μ(p + 2) = 1 and μ(p + 2) = −1 each have density 1/2 among the primes p with p + 2 squarefree; for h = 2 this implies
the bound above with X/log X in place of X/(log X)^300.

For h = −1 and an even number of prime factors, the statement that there are infinitely many such primes is
Theorem 1.1 of OpenAI's paper
[Prime Predecessors with an Even Number of Prime Factors](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Prime-Predecessors-with-an-Even-Number-of-Prime-Factors-September-17-2026/paper.pdf)
(17 September 2026). The proof applies the prime-slot correlation theorem of that paper and the sieve lemmas of
[Weighted dilation graphs, smooth shifted primes and totient fibers](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Weighted-Dilation-Graphs-Smooth-Shifted-Primes-and-Totient-Fibers-September-24-2026/paper.pdf)
(24 September 2026), and follows the argument of the first. For a general shift it adds a coprimality condition in
the Type II sum, expanded into Dirichlet characters of the rough variable, and the local factors at the primes
dividing 2h.

### [`tensor-contraction-consequences/`](tensor-contraction-consequences/) — Conditional consequences of a Boolean tensor-contraction theorem: threshold circuits and sparse connectivity

Paper (32 pages), 29 October 2026: [PDF](tensor-contraction-consequences/paper.pdf). Exhaustive finite checks of the reductions are in [`tensor-contraction-consequences/anc/`](tensor-contraction-consequences/anc/).

All results are conditional on the Boolean tensor-contraction theorem stated as Theorem D.1 of OpenAI's manuscript
[The Exponential Time Hypothesis is False](https://github.com/openai/math/blob/42907c9e999cc00d6abe7a50bfc1023250edd1b9/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf)
(25 October 2026, cited at commit `42907c9e`); the Lean formalization listed for that manuscript covers its fixed-width
counting theorem, not Theorem D.1. Under this hypothesis: deterministic approximate counting, with error as small as
2^(−S^(9/10)/log S), for integer-weight threshold circuits of arbitrary depth and fan-in in time 2^(O(S/√log S)),
S = inputs + wires, with a per-gate version that is exact when no gate is hashed; an E^NP language that needs more than
c·N·√(log N) wires for real-weight threshold circuits at every large input length, with a constant-advantage
average-case version (instantiating the algorithmic method of Williams and the frameworks of Chen–Williams,
Bathie–Williams and Chen–Lyu–Williams; it implies the every-length form of OpenAI's Corollary 1.4); and deterministic
2^(O(n/√log n)) algorithms with witness recovery for Hamiltonian cycle and path, longest path, TSP, Steiner tree,
feedback vertex set and connected vertex cover and dominating set on graphs with O(n) edges, with exact counting of
Hamiltonian cycles.

### [`zero-free-beyond-7-8/`](zero-free-beyond-7-8/) — A zero-free half-plane beyond 7/8

Paper (44 pages), 8 October 2026: [PDF](zero-free-beyond-7-8/paper.pdf). Exact-arithmetic certificates are in [`zero-free-beyond-7-8/anc/`](zero-free-beyond-7-8/anc/).

The Riemann zeta function, every Dirichlet L-function, and every finite-order Hecke L-function over Q(√−3) have no
zeros with Re s > σ†, where σ† = 0.8749570194… is the root in (0.8749570194, 0.8749570195) of

```math
7884\,s^3-18819\,s^2+14643\,s-3686=0 .
```

In particular there are no zeros with Re s > 43747851/50000000 = 7/8 − 2149/50000000.

The proof re-runs the argument of OpenAI's paper
[The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf)
with changed parameters, taking the statements of that paper as input. Freeing the skew parameter of the geometry
gives the endpoint σ\* = (1507 − 2√921)/1653 = 0.8749570698…; extending the range of the plain fourth-moment estimate
from κ ∈ [3/4, 1] to κ ∈ [37/50, 1] gives σ†. The intermediate rational value 20999/24000 = 7/8 − 1/24000, with the
skew parameter kept at 1/8, was obtained independently by Z. Gao
([A quantitative refinement of the seven-eighths zero-free half-plane](https://github.com/Gaozhongpai/seven-eighths-refinement-certificates), 7–8 October 2026). The endpoint σ\* was obtained
independently by B. Liu ([arXiv:2610.12234](https://arxiv.org/abs/2610.12234), 8 October 2026, with Lean files);
version 2 of that note (12 October 2026) states a boundary that agrees with σ† to the 18 digits shown there. Later preprints state smaller boundaries:
0.8748867 for Dirichlet L-functions and finite-order Hecke L-functions over Q(√−3) (Y. Xu and H. Sang,
[arXiv:2610.15291](https://arxiv.org/abs/2610.15291)), and 0.874886647… for finite-order Hecke L-functions over
every number field (B. Liu, [arXiv:2610.26835](https://arxiv.org/abs/2610.26835)).

### [`consequences/`](consequences/) — Consequences of results in the release

Twelve statements, each obtained by combining one theorem of the release with results in the literature, with the
release input, the bridging results and the deduction written out:

- deterministic construction of irreducible polynomials of every degree over prime fields;
- lower bounds for the number of Carmichael numbers and of Novak–Carmichael numbers;
- the Tate, Beilinson–Parshin and Lichtenbaum conjectures for varieties of abelian type over finite fields;
- failure of Tachikawa's first conjecture;
- Wall's question for hyperbolic groups, the torsion-free Kapovich–Kleiner conjecture and the toral relative Cannon conjecture;
- C\*-simplicity of Thompson's group T;
- surface group factors are isomorphic to the free group factor L(F₂);
- rank r Donaldson–Thomas invariants of Calabi–Yau threefolds from rank 0;
- ground configurations of the planar disordered Ising ferromagnet;
- the weak recovery threshold of the four-community stochastic block model;
- the quantum Fourier transform is not in QAC⁰;
- the Strong Non-Synthesis Conjecture of Lombardi–Ma–Wright.

Every statement is conditional on the release theorem named in its entry.

Each paper directory contains the PDF, the LaTeX source, and any ancillary files, with a README stating exactly which
statements are taken from the release and which deductions are new.

## Citation

Each paper directory has a BibTeX block in its README; please cite the individual paper. The repository as a whole can be cited through
[`CITATION.cff`](CITATION.cff) (the "Cite this repository" button on GitHub). The repository is archived by
[Software Heritage](https://archive.softwareheritage.org/browse/origin/?origin_url=https://github.com/aster2024/openai-math-followups);
the snapshot of 8 October 2026 is `swh:1:snp:b1621de1100454c3ee01cb5132e7508e92c6b7be`.

Results of the OpenAI release are cited in each paper by manuscript, pinned to the commit of
[github.com/openai/math](https://github.com/openai/math) at which they were read.

## Licence

The papers and text are under CC BY 4.0 (see [`LICENSE-papers.md`](LICENSE-papers.md)); the programs and Lean files in the `anc/` directories are under the MIT licence (see [`LICENSE`](LICENSE)).

## Use of AI

The proofs and the texts in this repository were produced with AI systems (GPT-6 Astra, GPT-6.1 Sol, Claude Fable 5.1, Claude Opus 5.5
and Claude Sonnet 5.5) under the author's direction. They were checked by independent reviews with AI models, by Lean where a
part is formalized, and by the computations in the ancillary directories. The author takes responsibility for the content.
