# Follow-ups to the OpenAI mathematics release

Notes and papers by Jizhou Guo (mitsuha2021b@gmail.com) that build on results of the
[OpenAI mathematics release](https://github.com/openai/math) of October 2026, pinned throughout to commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

## Contents

### [`almost-prime-pairs-reduction/`](almost-prime-pairs-reduction/) — Liouville signs at almost-prime pairs: a reduction to one inequality and two model sequences

Paper (36 pages), 10 October 2026: [PDF](almost-prime-pairs-reduction/paper.pdf).

Let h ≥ 2 be a fixed even integer, σ = c/log X, J_σ(n) = ∏_{p | n} (1 − p^(−σ)) and W(n) = J_σ(n)·J_σ(n + h). The sum
M₀ = Σ_{n ≤ X} W(n) has order X/(log X)², and the sums of λ(n)W(n) and of λ(n + h)W(n) are at most εM₀ in absolute
value when c ≥ c₀(ε). Consequently the single inequality

```math
\Bigl|\sum_{n\le X}\lambda(n)\,\lambda(n+h)\,W(n)\Bigr|\le(1-2\varepsilon)\,M_0\qquad\text{for all large }X
```

would give, for a fixed K, ≫ X/(log X)² integers n ≤ X with Ω(n), Ω(n + h) ≤ K for each sign pattern of
(λ(n), λ(n + h)). The paper does not prove this inequality; this part uses classical inputs only.

The paper also constructs two ±1-valued sequences. The first has square-root cancellation on intervals,
progressions, additive and character twists, fixed two-point sums and reflected sums, and its sieve remainder for
the pair (n, n + 2) at level X^θ is asymptotic to (c₂·log 2/32)·θ²·X·log X. The second has the corresponding
two-point, character and Type I bounds, and its Type II matrices (f(mℓ + h)) have operator norm ≫ √(MN)/log X on
infinitely many rectangles. A proof of the sieve remainder bound or of the Type II bound for λ therefore has to use
information beyond the listed estimates. The paper further classifies exact separated-variable substitutions and
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
primitive roots.

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

For h = −1 and an even number of prime factors, the statement that there are infinitely many such primes is
Theorem 1.1 of OpenAI's paper
[Prime Predecessors with an Even Number of Prime Factors](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Prime-Predecessors-with-an-Even-Number-of-Prime-Factors-September-17-2026/paper.pdf)
(17 September 2026). The proof applies the prime-slot correlation theorem of that paper and the sieve lemmas of
[Weighted dilation graphs, smooth shifted primes and totient fibers](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Weighted-Dilation-Graphs-Smooth-Shifted-Primes-and-Totient-Fibers-September-24-2026/paper.pdf)
(24 September 2026), and follows the argument of the first. For a general shift it adds a coprimality condition in
the Type II sum, expanded into Dirichlet characters of the rough variable, and the local factors at the primes
dividing 2h.

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
independently by B. Liu ([arXiv:2610.12234](https://arxiv.org/abs/2610.12234), 8 October 2026, with Lean files).

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

The proofs and the texts in this repository were produced with AI systems (GPT-6 Astra, GPT-6.1 Sol, Claude Opus 5.5 and
Claude Sonnet 5.5) under the author's direction. They were checked by independent reviews with AI models, by Lean where a
part is formalized, and by the computations in the ancillary directories. The author takes responsibility for the content.
