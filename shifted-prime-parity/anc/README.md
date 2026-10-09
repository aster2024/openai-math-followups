# Finite checks

Both programs use only the Python 3 standard library (Python 3.8 or later).
Run them from this directory; neither reads nor writes other files. They print
one summary line and fail on an assertion if an identity is violated.

```bash
python3 general_parametrisation.py
python3 general_local_conditions.py
```

`general_parametrisation.py` checks the forward bilinear identities, their
inverse, and the unit-ratio mask in Section 2, including both signs of the
shift. It retains the counterexample a=1, b=-6 to an oddness-only condition.
It uses a=1,...,6 and nonzero b in [-18,18], together with
±25, ±27, ±36, ±48, ±49, subject to gcd(a,b)=1. The forward enumeration
uses e=1,...,12, n=1,...,21, m,m'=1,...,31; the independent inverse and mask
enumerations use 0<|k|≤6, m,m'=1,...,24 and v=1,...,17. It also enumerates
residue pairs modulo 3,5,7,11,13 to check the local product identities.

`general_local_conditions.py` checks local units and obstructed prime forms
for a=1,...,8, nonzero b in [-24,24], and odd u in [1,99]. It checks product
roots modulo 3,5,7,9,15,25,35,49, and the local-factor ratio (ℓ-1)/(ℓ-2)
for ℓ=3,5,7,11,13,17,19. It also checks the cutoff and squarefree conversions
for 0<|h|≤50 and X=1000,2000,5000.

These finite enumerations concern the algebraic identities and local factors;
the analytic estimates and infinite prime counts are proved in the paper.
