# Finite identities

Both standalone programs use only the Python standard library, read and write no files, and print one summary line. Run sequentially:

```sh
python3 arithmetic_identities.py
python3 comparison_identities.py
```

`arithmetic_identities.py` checks finite instances of:

- (1.6): prime-square pair factors.
- (4.4): tilted padding characteristic coefficients.
- the three-site factor preceding (7.27): distinct-root triple factor.
- (7.24): closed arrival identity with repeated vertices.
- (7.18): the same balanced closed-weight identity, including zeros.
- (7.25): capped level-vector threshold.
- (10.4): local external-padding Euler identity.
- (10.5): Gaussian-rational modulus-square identity.
- (6.8): rough dilation.
- (7.29): soft high-prime dilation.
- (11.2): full-Omega dilation.
- the factorization n = uem preceding (11.5): common-prefix factorization.
- the threshold law preceding (9.11): geometric-threshold local acceptance.
- (6.17): sign-indicator expansion.
- (4.10): rational diagonal exponent.
- (8.9): tradeoff exponents.
- (9.7): real two-layer bilinear pairing.
- (10.16): finite Selberg divisor mass.
- (10.17): finite divisor inversion and quadratic diagonalization.
- (10.18): Selberg coefficient formula and bound.
- (10.19): finite Rankin product inequality at a rational test exponent.
- (10.20): finite marked-subset product expectation.
- the marking identity underlying (10.15): local marked-subset acceptance.

`comparison_identities.py` checks (3.2) (monotone decoded residue preimages), dyadic-prefix interval encoding in Proposition 3.3, and (3.5) (nonnegative low-order Walsh correction with exactly uniform selected marginals).

The checks concern finite algebra and encodings. The analytic estimates and uniform asymptotic bounds are proved in the paper from its stated inputs.
