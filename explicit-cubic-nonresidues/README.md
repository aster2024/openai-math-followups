# Explicit least prime ideals and cubic non-residues over Q(√−3) from a zero-free half-plane

Jizhou Guo  
mitsuha2021b@gmail.com

Let F = Q(√−3) and O = Z[ω]. Theorem 1.1 of OpenAI's paper of 30 September 2026 states that every finite-order Hecke L-function of F has no zero in Re(s) > 7/8. Taking this statement as a hypothesis (H_F), the paper proves, with every constant explicit:

- for every nonzero ideal m ≠ (1) of O and every proper subgroup H of the ray class group Cl_m there is a prime ideal p ∤ m whose class is not in H with

      N(p) < (36 log(3 N(m)) + 100)^8 ≤ (82 log(3 N(m)))^8;

- every ray class modulo m contains a prime ideal of norm less than (h_m (36 log(3 N(m)) + 100))^8, where h_m = |Cl_m| ≤ N(m); the factor h_m^8 cannot be replaced by any power of log N(m) (a pigeonhole argument shows that for a prime ideal q some class of Cl_q contains no prime ideal of norm ≤ (N(q) − 7)/12);

- for every nonzero prime ideal π ∤ 3 there is a prime ideal p ∤ 3π of norm less than (36 log(27 N(π)) + 100)^8 whose generator ≡ 1 (mod 3) is a cubic non-residue modulo π;

- for every a ∈ O that is not a cube there is a prime ideal p ∤ 3a with (a/p)_3 ≠ 1 and N(p) < (36 log(243 N(a)) + 100)^8; hence for every integer a that is not a perfect cube there is a prime p ≡ 1 (mod 3) modulo which a is not a cubic residue, with

      p < (36 log(243 a^2) + 100)^8 < (72 log|a| + 297.76)^8 ≤ (502 log|a|)^8.

The exponent is 8 = 1/(1 − 7/8), without ε: a smoothed explicit formula with the kernel 1/(s(s+1)) is moved to Re(s) = 1/16, past every nontrivial zero, and the zero sum is bounded by x^{7/8} · 18 log(3 N(f)) with no factor log x. The shape of the results and the exponent are Bach's: Bach (1982) proved the Dirichlet case with exponent 1/(1 − Θ) under any half-plane Re s > Θ, Θ < 1, with the same kernel, and Bach (1990, Theorem 4) gave explicit ERH constants over number fields; the GRH analogues over number fields are those of Lagarias–Odlyzko and Bach–Sorenson, with the exponent 2 replaced by 8 here. What is done here is to give fully explicit constants over Q(√−3) from the released theorem (including explicit zero-counting and log-derivative lemmas for Hecke L-functions over Q(√−3)), and to treat the Kummer-extension application with numbers, where the character p ↦ (a/p)_3 is a ray class character of F and not a Dirichlet character, so that the half-plane for Dirichlet L-functions alone does not suffice. No claim of novelty or priority is made; Section 12 of the paper records what each related source states, including Bach's theorems, the public Dirichlet analogue O((log q)^8), Hu's effective Chebotarev statement with exponent 8, the smaller boundaries announced since (which would lower the exponent to about 7.997 or 7.993), and the unconditional Chebotarev bounds. The input theorem is not verified here.

References to the OpenAI manuscripts use repository [openai/math](https://github.com/openai/math) at commit adc7f1241b42e322a6451854ab7e4b4c146bf78a:

- [The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf), September 30, 2026 (Theorem 1.1, the input).
- [Lean scope document, lean/docs/003.md](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/docs/003.md).

The Dirichlet analogue is cited from the README of [liouville-goldbach](https://github.com/aster2024/openai-math-followups/tree/main/liouville-goldbach) (Part II) and from B. Sandlund's memo in [brycesandlund/quasi-riemann-algorithms](https://github.com/brycesandlund/quasi-riemann-algorithms); the smaller boundaries from [zero-free-beyond-7-8](https://github.com/aster2024/openai-math-followups/tree/main/zero-free-beyond-7-8) (σ† ≈ 0.874957, Q(√−3)), from B. Liu, [arXiv:2610.26835](https://arxiv.org/abs/2610.26835) (B♭ ≈ 0.874887, every number field; abstract only, which attributes σ† to an earlier preprint of his) and from Cureton–Thorner, [Hexagon 2610.00200v1](https://hexagonmath.org/2610.00200v1) (31/32, every number field; abstract only). Hu's [Hexagon preprint 2610.00216v1](https://hexagonmath.org/2610.00216v1), which states the half-plane for unitary Weil L-functions over every number field and, in its Corollary 9.6, a prime ideal with prescribed Frobenius of norm ≪ (log(e d_L) + n_L)^8 with an unspecified constant, is described only by what it states. Bach's two papers were read in the transcriptions kept in Sandlund's repository. None of these is verified here.

Read [paper.pdf](paper.pdf). The complete LaTeX source is in [source/](source/). With Tectonic installed, compile from that directory:

    cd source
    tectonic main.tex

Alternatively, with pdfLaTeX: run `pdflatex main.tex`, `bibtex main`, and `pdflatex main.tex` twice.

From this directory, rerun the checks with Python 3 (mpmath, numpy, scipy, sympy); each script prints one summary line (`-v` for details), and `sh anc/run_all.sh` runs all of them and rewrites the `.out` files:

    python3 anc/constants.py
    python3 anc/digamma.py
    python3 anc/main_term.py
    python3 anc/lemma5.py
    python3 anc/kummer_conductor.py
    python3 anc/small_cases.py
    python3 anc/zetaF.py
    python3 anc/hecke_fe.py
    python3 anc/hecke_lines.py
    python3 anc/hecke_zeros.py

`constants.py` evaluates every numerical constant of the paper and the final inequalities of Theorems 1 and 2; `digamma.py` checks the digamma bounds on grids; `main_term.py` compares the smoothed prime-ideal sum with its main term x/2; `lemma5.py` and `kummer_conductor.py` check the ray-class character of the cubic symbol and the conductor of F(a^{1/3})/F; `small_cases.py` computes the least prime p ≡ 1 (mod 3) with a a cubic non-residue for all non-cubes 2 ≤ a ≤ 20000 (maximum 73, at a = 2478); `zetaF.py` and the three `hecke_*.py` scripts test the zero-count and log-derivative lemmas on ζ_F and on the cubic Hecke character (2/p)_3, including the functional equation with the archimedean factor Γ_C and conductor 108. Their outputs are in anc/ (see [anc/README.md](anc/README.md)). The scripts check arithmetic; the proofs are in the paper.

## Use of AI

The proofs and the text of the paper were produced with AI systems (Claude Fable 5.1 and Claude Opus 5.5) under the author's direction. They were checked by independent reviews with AI models and by the computations in the ancillary files. No human expert has reviewed them. The author takes responsibility for the content.

## Citation

```bibtex
@misc{Guo2026CubicNonresidues,
  author = {Guo, Jizhou},
  title = {Explicit least prime ideals and cubic non-residues over {$\mathbb{Q}(\sqrt{-3})$} from a zero-free half-plane},
  year = {2026},
  month = oct,
  note = {28 October 2026}
}
```
