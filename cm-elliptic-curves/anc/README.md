# Checks of explicit identities

These programs check finite identities used in the paper, exactly or to high precision. The analytic proofs are in
the paper.

Requirements: Python 3.10 or later with the packages in `requirements.txt`. Run from the directory that contains
`anc/`, one program at a time:

```sh
python anc/check_gauss.py
python anc/check_cusp.py
python anc/check_reflection.py --case 0
python anc/check_reflection.py --case 1
python anc/check_reflection.py --case 2
python anc/check_cm.py
python anc/check_full_theta.py
```

Each program takes a few seconds and writes its result to `anc/results/`.

| Program | What is checked | Scope and precision |
|---|---|---|
| `check_gauss.py` | The Gauss–Jacobi identities, the conjugate angular direction, every local exponent j = 0, …, 5 and all residue values including zero | Exact Jacobi sums; 75-digit Gauss sums and local transformations at norms 7, 13, 31, 25, 121 |
| `check_cusp.py` | Every generic Taylor monomial through degree 6 in the pure Wirtinger jet; the mixed height terms; the Lie-algebra calculation | Exact symbolic identities, generic in the complex denominator |
| `check_reflection.py` | The Bessel–Mellin normalization, the one-mode inverse-cusp reflection integrated directly, the scalar 1/81 and the gamma kernel | 60 digits; modes 1, 2, 4; denominators of λ-valuation 0, 1, 2 |
| `check_cm.py` | The sextic formula for the Frobenius trace of y² = x³ + D for nine values of D, the inert traces, the curve with D = 16 at the prime 2, and the conductor-one character of type 6 | 581 exact comparisons at primes up to 199: 188 pairs (D, p) with p split, checked at both primes above p, and 205 pairs with p inert (393 distinct point counts), and one comparison for D = 16 at the prime 2 |
| `check_full_theta.py` | The level-one completed reflection with the three cusp Fourier expansions, for the correct kernel index and, as a control, for a wrong one | Double precision with truncated sums and quadrature; X = 20; modes 1, …, 4 |

`eisenstein.py` (exact arithmetic) and `eisenstein_float.py` (floating point) are small libraries for the Eisenstein
integers used by these programs.
