# Follow-ups to the OpenAI mathematics release

Notes and papers by Jizhou Guo (Dots Studio, Rednote; mitsuha2021b@gmail.com) that build on results of the
[OpenAI mathematics release](https://github.com/openai/math) of October 2026, pinned throughout to commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

| Directory | Result | Status |
|---|---|---|
| [`liouville-goldbach/`](liouville-goldbach/) | **Goldbach-type representations with prescribed Liouville signs.** For every sufficiently large integer $N$, each of the four sign patterns $(\lambda(a),\lambda(b))$ with $a+b=N$ occurs $N/4+O(N(\log N)^{-c})$ times; equivalently $\sum_{n<N}\lambda(n)\lambda(N-n)=O(N(\log N)^{-c})$, which proves the conjecture of Corrádi and Kátai for the Liouville function. Part II: consequences of the zero-free half-plane $\operatorname{Re}s>7/8$ (Goldbach exceptional set, least prime in a progression, least non-residues, least primitive roots). | Paper (28 pages), 8 October 2026 |

Each directory contains the PDF, the LaTeX source, and any ancillary Lean files, with a README stating exactly which
statements are taken from the release and which deductions are new.

## Use of AI

AI systems, including GPT-6 Astra, GPT-6.1 Sol and Claude Opus 5.5, were used in developing the proofs and preparing the manuscripts.
The author takes responsibility for the content.
