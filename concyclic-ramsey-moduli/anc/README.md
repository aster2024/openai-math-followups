# Exact arithmetic checks

Python 3 and SymPy (see `requirements.txt`); everything else is in the standard library, including
`fractions.Fraction`. No floating-point arithmetic is used. Run one command at a time from this directory (`anc/`),
since the programs write their receipts to `checks/` and `check_manuscript.py` reads them:

```sh
nice -n 19 python3 checks/identities.py
nice -n 19 python3 checks/structure.py
nice -n 19 python3 checks/eight_factory.py
nice -n 19 python3 checks/second_jet_certificate.py
nice -n 19 python3 checks/elliptic.py
nice -n 19 python3 check_manuscript.py
```

Each program prints lines beginning with `PASS:` and normally runs in a few seconds.

| Program | What it checks | Receipt |
| --- | --- | --- |
| `checks/identities.py` | The homogeneous determinant and circle-kernel identities; two exact seven-node tests of the barycentric moment identities (spatial trace exactly 4). It also checks that an auxiliary prime modulus is prime; this is not used in the paper. | `checks/identities.json` |
| `checks/structure.py` | The 64 seven-node sign spaces and their projection-rank counts 1, 7, 21, 35; that the velocity space of the Appendix E family lies in none of them at the test values; the algebraic-diagonal certificate of Section 5. | `checks/structure.json` |
| `checks/eight_factory.py` | The 128 eight-node sign spaces with dim(U + TU) = 4, and the two-group graph identity. It imports `structure.py`. | `checks/eight_factory.json` |
| `checks/second_jet_certificate.py` | The 10 × 10 augmented minor of Section 6: det M = 1/30611001600000 and det(720M) = 1223059046400000 by two algorithms; a left null vector showing the rank gap 9 → 10; direct second-order consistency checks for 6, 7 and 8 nodes. | `checks/second_jet_certificate.json` |
| `checks/elliptic.py` | The curve-map, pair-invariant and biquadratic identities of Section 7; 21 exact rational tests of the pair invariant; the eight rational orbit points and all 35 cross-ratio differences. The receipt contains both polynomial quotients. | `checks/elliptic.json` |
| `check_manuscript.py` | That the matrix, the eight fractions, the 35 signs and the two polynomial quotients printed in the LaTeX source equal the receipts above; that all labels are unique, all references resolve and every bibliography entry is cited. | `manuscript-check.json` |

The rational test values are tests of finitely many rational expressions. They are not specializations of the
function fields in the paper and say nothing about the Ramsey property of the rational configurations used. The
classification of isotropic subspaces is proved in the paper; the enumerations above are checks of it on examples.
