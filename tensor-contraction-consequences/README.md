# Conditional consequences of a Boolean tensor-contraction theorem

Jizhou Guo  
mitsuha2021b@gmail.com

Read [paper.pdf](paper.pdf). The complete LaTeX source is in [source/](source/), and the finite checks are in [anc/](anc/).

## Result

Assuming the Boolean tensor-contraction theorem stated as Theorem D.1 in OpenAI's manuscript of 25 October 2026 (H_TC), the paper proves:

- Deterministic acceptance-probability approximation for integer-weight threshold circuits of arbitrary depth and fan-in, with polynomial description length, in polynomial space and time `poly(S+L) · 2^{O(S/sqrt(log S))}`, where `S = n+w+2`. The absolute error may be as small as `2^{-S^{9/10}/log_2(S+16)}`. A unified per-gate theorem includes exact-threshold and weighted modular gates under explicit parameter budgets; when no gate is hashed, the count is exact and the description length may be arbitrary.
- Real-weight threshold-wire lower bounds in `E^NP` of more than `c N sqrt(log N)` wires, at every sufficiently large input length, together with infinitely-often and fixed-advantage average-case versions.
- Deterministic polynomial-space algorithms taking `poly(n+L) · 2^{O(n/sqrt(log n))}` time on graphs with `O(n)` edges for Hamiltonian cycles and paths, longest paths, TSP, Steiner tree, feedback vertex set, connected vertex cover, and connected dominating set, with witness recovery. The paper specifies exact-counting conventions, directed variants, shortest-path-metric TSP and Rural Postman, and nonnegative costs of up to `ceil(n^{9/10})` bits.

Every algorithmic and complexity-theoretic conclusion is conditional on its stated input. The paper supplies reductions and parameter bookkeeping; the finite checks concern those reductions.

## Input

References to the input manuscript and its Lean scope document use [openai/math](https://github.com/openai/math) at commit `42907c9e999cc00d6abe7a50bfc1023250edd1b9`:

- [The Exponential Time Hypothesis is False](https://github.com/openai/math/blob/42907c9e999cc00d6abe7a50bfc1023250edd1b9/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf), dated 25 October 2026: Theorem D.1 is H_TC; Theorem 1.1 is the fixed-width counting hypothesis H_BB; Corollary 1.4 states the infinitely-often lower bound for fan-in-two Boolean circuits.
- [Lean scope document, lean/docs/378.md](https://github.com/openai/math/blob/42907c9e999cc00d6abe7a50bfc1023250edd1b9/lean/docs/378.md): its scope is the fixed-k exact-counting statement, with the bounds specified there. It does not cover H_TC or the two sharper counting bounds in the October 25 manuscript. The formalization is not rerun here.

The main results use the stronger input H_TC. The paper's short chromatic-number discussion is conditional on H_BB alone.

## Related work

The circuit lower-bound arguments instantiate Williams' [algorithmic method](https://doi.org/10.1137/10080703X), the PCP-of-proximity framework of [Chen–Williams](https://doi.org/10.4230/LIPIcs.CCC.2019.19) and [Bathie–Williams](https://doi.org/10.4230/LIPIcs.ITCS.2024.10), and the refuter and amplification constructions of [Chen–Lyu–Williams](https://eccc.weizmann.ac.il/report/2020/150/). OpenAI's own Corollary 1.4 uses the fixed-density case of H_BB to obtain an infinitely-often fan-in-two gate bound of the same order. Theorem 1.2 of this paper, under H_TC, implies its every-sufficiently-large-length and constant-advantage forms, since a fan-in-two Boolean gate has a threshold implementation using at most five wires. The reverse generic simulation does not recover the threshold-wire bound from Corollary 1.4.

The comparison protocol follows Nisan's integer-comparison construction, with [Viola's addition and comparison protocols](https://doi.org/10.1007/s00493-014-3078-3) as related work. For connectivity, the paper compares [Cut&Count](https://doi.org/10.1109/FOCS.2011.23), [determinant and matrix-tree methods](https://doi.org/10.1016/j.ic.2014.12.008), and [Björklund's Hamiltonicity algorithm](https://doi.org/10.1137/110839229). The paper also describes the depth restrictions and gate/wire measures in the threshold-circuit results of Impagliazzo–Paturi–Saks, Kane–Williams, and Chen–Tal–Wang, and the binary-basis gate bound of Li–Yang.

## Build and checks

With Tectonic installed, compile from the source directory:

```bash
cd source
tectonic main.tex
```

Alternatively, run `pdflatex main.tex`, `bibtex main`, and `pdflatex main.tex` twice. An offline Tectonic build requires its TeX bundle and fonts to be cached beforehand; use `tectonic -C --untrusted --keep-logs --keep-intermediates main.tex` with that cache.

From this directory, run the finite checks with Python 3, NumPy, a C++17 compiler (`g++`), and a POSIX environment:

```bash
nice -n 19 bash -c 'ulimit -v 8388608; timeout 900s python3 -B -I anc/run_all.py'
```

The runner executes 24 checks serially and cleans up temporary executables. [anc/README.md](anc/README.md) gives the coverage and exact-arithmetic bounds. Each check prints one summary line; details, resource records, source hashes, and relative commands are in `anc/results/`. These finite computations do not establish H_TC or its asymptotic running time and do not replace the proofs.

Verify the distributed files from this directory with:

```bash
sha256sum -c SHA256SUMS
```

Rerunning the checks replaces the recorded results and their timings, so verify the distributed checksums before rerunning them.

## Use of AI

The proofs and the text of the paper were produced with AI systems (GPT-6.1 Sol, GPT-6 Astra, Claude Opus 5.5, and Claude Fable 5.1) under the author's direction. They were checked by independent reviews with AI models and by the computations in the ancillary files. No human expert has reviewed them. The author takes responsibility for the content.
