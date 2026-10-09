# Finite identity checks

Both programs use only the Python 3 standard library. Run them from this directory; neither reads nor writes
other files. Each prints one summary line and fails on an assertion if an identity is violated.

```sh
python3 reflected_identities.py
python3 rough_convolution.py
```

`reflected_identities.py` checks finite instances of the following identities: reserved-prime extraction with
prime powers (Lemma 4.1), the small-prime convolution (Lemma 3.3), the group local expectation (Proposition 6.1),
reflection (Proposition 2.6), quotient blocks (Proposition 2.5), the shared-label normalization
(Proposition 5.2), and the completely multiplicative character example (Remark 7.1).

`rough_convolution.py` checks the identity lambda R_z = lambda * g_z of Corollary 3.4, including prime powers.

These programs check finite algebraic identities; the analytic estimates are proved in the paper.
