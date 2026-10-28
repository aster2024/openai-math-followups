# Ancillary scripts

Python 3 with `mpmath`, `numpy`, `scipy` and `sympy`. Each script prints exactly one summary line (`OK` or `FAIL` plus the key numbers); `-v` prints the details. `sh run_all.sh` runs all of them and writes `<name>.out` next to each script (every run takes under 20 seconds). Section and lemma numbers refer to the paper.

| Script | What it checks | Output |
|---|---|---|
| `constants.py` | −ζ_F'/ζ_F(2) (two ways), log 2π, I_0, I_1, every constant in Lemmas 4.1, 5.1, 6.2, the final inequalities of Theorems 1 and 2 on a grid of L and h, 36 + 100/log 9 ≤ 82, c_0 = 36 log 243 + 100 < 297.76, 72 + 297.76/log 2 ≤ 502, and the exponents 1/(1−θ) for θ = σ†, B♭ | `constants.out` |
| `digamma.py` | Lemma 3.1 (a)–(d) on 7800 heights t ∈ [0, 2010] and 125 values of σ; Binet's second formula at six points | `digamma.out` |
| `main_term.py` | S_1(x) = Σ Λ(a)(1 − Na/x)_+ from a prime sieve against x/2 and Proposition 6.4, x = 10^4 … 10^7 | `main_term.out` |
| `lemma5.py` | Lemma 9.2: ψ_π is constant on ray classes mod 3π, multiplicative, takes all three values (eight primes π, split and inert); λ-part of its conductor (Remark 9.4) | `lemma5.out` |
| `kummer_conductor.py` | Lemma 10.1: empirical conductor of F(a^{1/3})/F for 18 values of a on prime ideals of norm ≤ 60000 (λ-exponent ≤ 4, tame primes exponent 1) | `kummer_conductor.out` |
| `small_cases.py` | Section 11.1: least p ≡ 1 (mod 3) with a a cubic non-residue for all non-cubes 2 ≤ a ≤ 20000 against the bound of Corollary 4′; records; inert-prime remark; prime-ideal version of Theorem 4 | `small_cases.out` |
| `zetaF.py` | (B1_F), (B2_F) for ζ_F on t ∈ [0, 40]; zero count of ζ_F in windows of radius 1 against Lemma 4.1(b) | `zetaF.out` |
| `hecke_fe.py` | Section 11.2: functional equation of L(s, χ_2), χ_2(p) = (2/p)_3, as θ(1/y) = y θ(y) with D = 108 (and failure for wrong D) | `hecke_fe.out` |
| `hecke_lines.py` | (B1), (B2) for L(s, χ_2) at ten heights | `hecke_lines.out` |
| `hecke_zeros.py` | critical-line zeros of L(s, χ_2) up to height 16 against Lemma 4.1(b) | `hecke_zeros.out` |

Libraries (no output): `zw.py` (arithmetic in Z[ω], ideal reduction, cubic residue symbol, generator ≡ 1 mod 3, prime elements) and `hecke_chi2.py` (Dirichlet coefficients of L(s, χ_2)).

The scripts check arithmetic and sanity; the proofs are in the paper, and the hypothesis (H_F) is not checked anywhere.
