# Exact-arithmetic certificates

From this directory, run:

    python3 anc/run_all.py

Python 3.9 or later and its standard library suffice. All checks run serially
in one process; the expected total is 214 PASS. The runner rewrites the five
verify_*.out.txt files and receipt.json.

- verify_rational.py: rational stages, geometry, and the conditional endpoint algebra.
- verify_quadratic.py: identities and inequalities in Q(sqrt(921)).
- verify_cubic.py: cubic-field identities, root isolation, and rational intervals.
- verify_structure.py: multivariate identities, coefficient formulas, and transform ledgers.
- verify_phases.py: exact conjugation, local-table, and zero-preserving divisor checks.
- exact.py: rational, polynomial, quotient-field, and interval arithmetic.

The scripts verify algebra and rational intervals; the analytic proofs are in
the paper. Hypothesis 11.1, the mean-square estimate for H >= D^(99/100), is
unproved; its polynomial certificate checks only the conditional calculation.
