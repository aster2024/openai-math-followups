# Ancillary finite checks

Python 3, standard library only. From this directory:

```sh
nice -n 19 python3 -I check_blocks.py
nice -n 19 python3 -I check_roots.py
```

`check_blocks.py` checks exact determinant transport, the unit-chart line and block counts, both forms of the parity condition, the all-integer nonnegative square, and the complex endpoint conjugation. It includes small explicit cases of the parity condition and of a labelled lattice overlap.

`check_roots.py` compares inverse-formula root enumeration with direct congruence enumeration for six small even totals, checks both swapped-complement floor branches, counts every determinant coset and first-row kernel for primes up to 7, and checks the local factors by exact rational arithmetic.

These are finite algebra and counting checks. They do not verify the asymptotic estimates of Lemma R, the LWW operator arguments, zero-free inputs, or the main theorems. Each program prints one summary line and normally runs in a few seconds.
