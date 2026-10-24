# Ancillary checks

These programs accompany the paper. They check finite identities and selected numerical integrals; the analytic
theorems rest on the arguments and stated inputs in the paper.

They need Python 3, SymPy and mpmath. Run them from this directory:

```bash
export SYMPY_GROUND_TYPES=python
python3 check_chain_independent.py
python3 check_cm_quartic_independent.py
python3 check_cubic_calibration_F.py
python3 check_transfer_preimages.py
python3 check_reflection_phase_separation.py
python3 check_finite_gauss.py
python3 check_pairing_crt_independent.py
python3 check_archimedean.py
python3 check_weyl_hankel_independent.py --mode 0 --rho 0.7
python3 check_weyl_hankel_independent.py --mode 1 --rho 0.7
python3 check_weyl_hankel_independent.py --mode 2 --rho 0.7
python3 check_weyl_hankel_independent.py --mode 2 --rho 1.3
python3 check_weyl_hankel_independent.py --mode 3 --rho 0.7
```

Each program prints one summary line and writes a full report to `results/`; a failed assertion stops it with a
nonzero exit code, and the summary line is printed only after all its assertions have passed. Setting
`SYMPY_GROUND_TYPES=python` selects SymPy's Python ground types, so the optional flint backend is not needed. The
CRT program takes about a minute; the others take seconds.

## Programs and scope

| Program | What it checks | What it does not check |
|---|---|---|
| check_chain_independent.py | Exact discriminant 144, relative discriminant norm 9, 50 local tame-character cases, 24 Jacquet indices, local signed sums, scale and amplification arithmetic. | General global theta existence, the analytic orbital Poisson formula, the mean square or zero-freeness. |
| check_finite_gauss.py | Exact cyclotomic arithmetic over residue fields of sizes 13, 25, 49, 121 and 37: Gauss–Jacobi, duplication, local unit powers and reflection support. | All residue fields, or any global analytic assertion. The general identities are proved in the paper. |
| check_cubic_calibration_F.py | Twenty exact cases for actual residue types of Q(ζ₁₂), both cubic embeddings, primary normalization and the relative residue-degree-two lifting sign. | Global representation theory or the asymptotic argument. |
| check_reflection_phase_separation.py | 13,824 formal three-prime configurations: common phases with shared squarefree and cube primes, inactive labels and collision zeros. | Automorphy or a large-sieve estimate. Infinite-order character values remain formal factors. |
| check_transfer_preimages.py | Complete finite local inverse maps for the two transformations and the initialization; detects the extra coprimality restriction between t and the row. | Analytic convergence, row kernels or infinite moment estimates. |
| check_pairing_crt_independent.py | Two-prime exact CRT arithmetic in a cyclotomic field of degree 864, both Gauss conversion directions, the initialization and 7,696 finite Poisson and exclusion cases. | The general orbital Poisson theorem or the theta datum. |
| check_cm_quartic_independent.py | Sixteen rational dyadic classes, all 64 unit residues per class, every multiplication pair, minimal-conductor witnesses, generator values and 864 good-prime Euler comparisons for 22 parameters. | Deuring's theorem or the local fourth-power bound on U₇, which are supplied by the paper and its classical inputs. |
| check_archimedean.py | Four Bessel–Mellin modes at 45 decimal digits, relative-error threshold 10⁻²⁸. | Interval certification, all parameters or the global reflection. |
| check_weyl_hankel_independent.py | A direct lower-root Jacquet/Hankel calculation, independent of the upper/lower Lie identity, at 40 digits, for (mode, radius) = (0, 0.7), (1, 0.7), (2, 0.7), (2, 1.3), (3, 0.7). | Interval certification or any global moment. |

The finite identities are checked exactly for the stated cases. The numerical quadratures have the stated precision
and tolerance and are not interval certificates. The global theta representation, the infinite mean squares, the
Poisson theorem and the zero-free half-planes are proved in the paper from its stated inputs.
