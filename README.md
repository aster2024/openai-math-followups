# Follow-ups to the OpenAI mathematics release

Notes and papers by Jizhou Guo (Dots Studio, Rednote; mitsuha2021b@gmail.com) that build on results of the
[OpenAI mathematics release](https://github.com/openai/math) of October 2026, pinned throughout to commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

## Contents

### [`liouville-goldbach/`](liouville-goldbach/) — Goldbach-type representations with prescribed Liouville signs

Paper (28 pages), 8 October 2026: [PDF](liouville-goldbach/paper.pdf).

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
([A quantitative refinement of the seven-eighths zero-free half-plane](https://github.com/Gaozhongpai/seven-eighths-refinement-certificates), 7–8 October 2026).

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

## Use of AI

AI systems, including GPT-6 Astra, GPT-6.1 Sol and Claude Opus 5.5, were used in developing the proofs and preparing the manuscripts.
The author takes responsibility for the content.
