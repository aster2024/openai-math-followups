# Ancillary checks

These programs verify exact algebra, rational exponent calculations and finite
examples used in the paper. They require Python 3.9 or later and SymPy.

From the root of the paper directory, run:

```sh
python3 anc/run_all.py
```

The runner executes three checks serially, with a 120-second timeout for each.
Each check prints one summary line and saves its detailed result under
`anc/results/`; the runner prints one final summary and writes
`anc/results/run_all.json`. Output locations are relative to the programs, so
the checks can also be run from another working directory. Assertions must be
enabled: use ordinary `python3`, without `-O`. The runner disables Python
bytecode writes in its child processes.

| Program | Scope |
| --- | --- |
| `exact_checks.py` | The quadratic and cubic polynomial identities; the rational κ = 899/2000 choice recorded in Section 2; fixed and moving cubic examples. |
| `interface_checks.py` | The transfer exponents; the change from 19/24 to 7/12 with the restricted Perelli–Pintz sum; the two-prefix arc comparison; 1940 integer triples for coefficient reconstruction. |
| `verify_claims.py` | The exponent calculations; pair-sum multiplicities for six quadratics and five cubics on 1 ≤ m ≤ 120; both cubic V = 0 branches when present; 15136 integer triples with 2 ≤ X ≤ 30; the moving cubic example and prime-scale bounds. |

For example, run one check with:

```sh
python3 anc/verify_claims.py
```

The finite examples supplement the arguments for general parameters given in
the paper. The external analytic inputs are stated in Section 2, and the
deductions from them are proved in Sections 3–6. The appendix describes these finite checks.
