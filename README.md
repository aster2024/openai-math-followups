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

Each directory contains the PDF, the LaTeX source, and any ancillary Lean files, with a README stating exactly which
statements are taken from the release and which deductions are new.

## Use of AI

AI systems, including GPT-6 Astra, GPT-6.1 Sol and Claude Opus 5.5, were used in developing the proofs and preparing the manuscripts.
The author takes responsibility for the content.
