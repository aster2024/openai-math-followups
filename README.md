# Follow-ups to the OpenAI mathematics release

Notes and papers by Jizhou Guo (mitsuha2021b@gmail.com) that build on results of the
[OpenAI mathematics release](https://github.com/openai/math) of October 2026, pinned throughout to commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

## Contents

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

### [`liouville-goldbach/`](liouville-goldbach/) — Goldbach-type representations with prescribed Liouville signs

Paper (28 pages), 8 October 2026: [PDF](liouville-goldbach/paper.pdf). Lean 4 formalization of the main theorem (with the
exponent c = 10⁻²⁰⁰), conditional on two published estimates: [`liouville-goldbach/lean/`](liouville-goldbach/lean/).

Let λ be the Liouville function. For every sufficiently large integer N, each of the four sign patterns
(λ(a), λ(b)) with a + b = N occurs N/4 + O(N (log N)^(−c)) times. Equivalently,

```math
\sum_{1\le n\lt N}\lambda(n)\,\lambda(N-n)=O\left(\frac{N}{(\log N)^{c}}\right),
```

which proves the conjecture of Corrádi and Kátai for the Liouville function.

Part II gives consequences of the zero-free half-plane Re s > 7/8 for Dirichlet L-functions: the exceptional set
in the binary Goldbach problem, the least prime in an arithmetic progression, least non-residues, and least
primitive roots.

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
independently by B. Liu ([note with Lean files](https://github.com/liubaiying101/Slightly-improved-zero-free-half-planes-for-the-quasi-Riemann-hypothesis), 8 October 2026).

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
