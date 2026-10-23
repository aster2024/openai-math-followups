# Ancillary finite checks

Python 3, standard library only. Most calculations use exact integer or
rational arithmetic. `check_blocks.py` also uses Python complex arithmetic
and a tolerance of `1e-10` for its square-positivity comparison.
`check_vaughan.py` represents logarithms by vectors of prime exponents.
No model, network access, external data or cluster is needed.

From this directory, run the programs serially:

```sh
for program in check_*.py; do
  nice -n 19 bash -c 'ulimit -v 8388608; timeout 900s python3 -I "$1"' _ "$program" || exit 1
done
```

Every program prints one summary line. The newer programs also save detailed
JSON receipts beside their source files. A failed assertion or a timeout is a
failed check; an existing receipt from an earlier run does not override it.

| Program | What it checks | Limits of the check |
|---|---|---|
| `check_blocks.py` | The retained v1 determinant transport, unit-chart blocks, parity, all-integer square and complex endpoint conjugation. | Small finite lattices and list models only. |
| `check_roots.py` | The retained v1 inverse/direct root enumeration for six small even totals, both positive-determinant swap branches, determinant cosets and first-row kernels at primes at most 7. | Does not estimate root discrepancy. Signed swaps are tested separately below. |
| `check_affine_geometry.py` | Both determinant signs, normalized bases, coordinate/primitivity/parity identities, the three swap branches `-1,0,1`, and the cofactor equation in both orientations. | Finite algebra, not uniform slope occupancy or analytic estimates. |
| `check_rough_and_parameters.py` | Finite CRT rough and squarefree factors, weight/cofactor identities for Möbius and Liouville, and rational margins for the earlier `a<1/3` fallback. | Its fallback parameter table alone does not establish the final `a<1/2` range. |
| `check_positive_memory.py` | The original exact factorial-measure adjoints and canonical/enlarged memory sums; rational margins for the final half-exponent parameter choice. | One group, `J=0`, two primes, memory cap 2, two/four edges. Cross-edge exclusion forces alternating sequences; this program alone does not test shared lists, longer internal gaps or never-active primes. |
| `check_shared_memory.py` | Independent direct time histories versus append/recall at `J=1`, three primes, two/four/six edges; complete measure ratios, repeated token types, active/memory overlaps and projective infinity. | A finite one-group model with cap 2, not an operator bound for all paths. |
| `check_forward_histories.py` | An independent delayed-charge oracle and forward product majorant: `J=1` through six edges, `J=2` and `K=2` through twelve edges, and a full CRT fixture through eight edges. | This tests forward-history inequalities, not the multi-group adjoint or arithmetic root transfer. |
| `check_inactive_bonferroni.py` | Joint projective-line enumeration in a five-prime pool, including never-active primes, endpoint square-root damping, and degree 1/2/3 Bonferroni remainders. | Independent-line expectations only; the arithmetic discrepancy is a separate proof step. |
| `check_progression_identities.py` | The progression Euler factors including forced zeros, the nonunit Möbius identity, and the finite congruence/divisibility identities used by the progression proof. | Does not test cancellation or distribution in progressions. |
| `check_vaughan.py` | The exact convolution identity at 5,400 parameter/integer pairs, both distinct prime-power corrections at 48 interval choices, and 2,304 complete-multiplicativity checks for the sifted indicator. | Does not check the smoothing estimate, Bombieri–Vinogradov, Type II or prime cancellation. |

These checks do not verify asymptotic estimates, Kloosterman estimates,
root-counting errors, signed memory/operator arguments, zero-free regions,
H1, H2′, LS(c), or any main theorem. The paper supplies general arguments
for the finite-model bounds and keeps the analytic and H2′ inputs explicit.
