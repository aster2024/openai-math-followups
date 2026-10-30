# Finite checks for the tensor-contraction reductions

From the directory containing this `anc/` folder, run:

```bash
nice -n 19 bash -c 'ulimit -v 8388608; timeout 900s python3 -B -I anc/run_all.py --part baseline'
nice -n 19 bash -c 'ulimit -v 8388608; timeout 900s python3 -B -I anc/run_all.py --part layers'
nice -n 19 bash -c 'ulimit -v 8388608; timeout 900s python3 -B -I anc/run_all.py --part residues'
```

Requirements: Python 3, NumPy, a C++17 compiler named `g++`, and a POSIX environment. The runner compiles two C++ programs in a temporary directory, runs 47 checks serially, and removes the temporary executables. It enforces niceness 19, an 8 GiB address-space limit, a 900-second timeout per child, and one native thread per child. Each displayed command bounds one batch by 900 seconds. Run all three in order; the baseline batch resets results, and the others retain verified records. The suite.json success record is created only when all 47 checks and both compilations have valid completed logs. Add --resume to a batch command to verify and skip its already completed rows, provided the check-source hashes match. No network access is needed. Each check and the runner print one summary line. Detailed outputs are written to `results/`.

`results/suite.json` records the suite outcome, resource limits, and source hashes. `results/manifest.json` records relative commands, exit codes, elapsed times, stdout line counts, and log hashes. `provenance.json` lists source filenames, hashes, and output conventions. Rerunning the suite replaces `results/`; commands in the manifest are relative to `anc/`. The temporary executable directory recorded there is created and removed by the runner.

| Program / invocations | Paper location | Finite coverage |
| --- | --- | --- |
| `finite_audit.cpp sign` | Section 6.1 | All permutations and contiguous row/column partitions through order 7: 21,413,481 exact integer inversion identities. |
| `finite_audit.cpp marker` | Section 6.2 | 254,254 undirected selected-vertex/marker configurations through 5 vertices; exact determinants, augmented spanning trees, and the forest condition. |
| `finite_audit.cpp directed` | Section 8 | 333,544 directed configurations through 4 vertices; determinants, acyclic outgoing choices, and marker reachability. |
| `p6_sign_check.py 1 300`, `2 300` | Section 6.1 | Fixed-seed sampled sparse supports, exhausting supported permutations and position-bit assignments on the smaller supports: 16,362 identities, 350 factor sums, including 218 parity-wire sums. |
| `p6_blockcount_check.py` | Section 6.1 | 20,000 fixed-seed random degree sequences, including heavy-tailed sequences; contiguous-block invariants and the count bound. |
| `p7_p8_filter_check.py 3`, `4` | Sections 6.2, 7, 8 | Exhaustive candidate choices on 120 sampled undirected and 76 sampled directed graphs, plus 68 sparse-metric-TSP comparisons. |
| `e2e_hc_network.py` | Section 7 | Nine graph/block-budget combinations, including disjoint triangles; full sign-factor sum, modular readback, integer division, and independent Hamiltonian-cycle enumeration. |
| `hc_accounting.py` | Sections 6.1, 7 | Actual ports, edges, and vertices on five sparse fixtures; approximately 42.8–52.4 wires per graph scale. These are finite examples of the accounting. |
| `c2_p2_p3_check.py` | Section 10.2 | Consistent-cut multiplicities, parity Hamiltonian-cycle layers, and marker-forest conditions. |
| `check_gadgets.py` | Sections 4.1, 4.3 | 9,000 arithmetic replays of sliced threshold, equality, modular, carry, quotient, and one-sided residue-hash formulas. Enumerates small modular truth tables for fan-ins 1, 2, 3 and modulus bounds 80, 60, 20. No tensor contraction or general integer-representation construction is performed. |
| `protocol_exact_check.cpp 2` | Section 3.1 | Two parties, eight-bit inputs, 2,048 primes; exact seed-suffix dynamic programming on 3,346,110 nontrivial state/threshold classes plus symbolic boundaries. Covers all 65,536 ordered input tuples via column symmetry. Maximum error 3071/2097152, below 1/2. |
| `check_contraction_engine.py` | Section 3.2 | 300 small factor systems compared with direct enumeration, checking the exact elimination helper. |
| `tensor_realization_check.py` | Section 3.2 | Explicit local transcript tables, equality trees, bipartite subdivision, and every private input/output; includes a freed-padding negative control. |
| `tensor_realization_t3_check.py` | Section 3.2 | A three-party explicit-table protocol network with equality fan-out and all private inputs. |
| `p11_tensor_check.py one_round_bad_seed`, `initial_stop`, `two_rounds` | Section 3.2 | Explicit arithmetic-gate tensors; exact elimination checks unique extensions, a wrong-hash seed, and early stopping. Each fixture has its own JSON result. |
| `p11_middle_stop.py` | Section 3.2 | An arithmetic-gate protocol fixture stopping between two rounds. |
| `check_unused_inputs.py` | Section 2.1 | Constant/identity functional relations with 0–4 declared inputs, before and after output pinning; includes two declared inputs with output equal to the first input and accepting count 2. |
| `check_G1_tensor.py` | Section 4.1 | 260 sampled instances, exhausting every input and full auxiliary code domains: 3,816 consistent-input contractions and 411 independently assigned slice-copy cases. |
| `check_G3_tensor.py` | Section 4.3 | 136,896 instance/input/prime combinations from 400 sampled instances, every input, and 24 primes; full residue code domains, unique extensions, one-sided error, and the bad-prime bound. |
| `check_thresholds.py` | Section 4 | A finite floating-point scan of sufficient-large-scale inequalities. This diagnostic does not prove an eventual threshold. |

The sliced-gadget and residue-chain checks use NumPy `int64` tensors. In the sliced fixtures the fan-in is at most 5 and all original slice inputs are fixed. Every auxiliary relation is a partial function in a directed acyclic graph once the quotient is fixed. During a partial contraction, a defining factor outside the contracted subset keeps its signal on the boundary; internal assignments are determined by boundary values and at most eight quotient codes. Thus intermediate counts are at most 8. In the residue chains, each transfer row and reachable state vector has at most one nonzero entry, equal to 1. The integer arithmetic is therefore exact on these fixtures. These two checks use shared word-valued variables; the protocol checks separately exercise Boolean equality-tree expansion and bipartite subdivision.

The permutation/partition and bounded marker families are exhaustive. Several Python programs exhaust assignments within fixed-seed sampled instances. These computations check finite instances of the reductions. They do not run the algorithm asserted by H_TC, do not test its asymptotic running time, and do not replace the written proofs.

## Version 2: fixed-width counting reductions

The following additions check Section 9 using literal-level exhaustive counting. They do not implement the fast counting algorithm assumed there. `cnf_circuits.py` supplies functional Boolean circuits and their complete 3-CNF equivalences; `check_cnf_reference.py` supplies a separate bitset Shannon counter and graph references. Helpers are imported by the check programs and do not print summaries. Each invoked check prints exactly one JSON summary line, retained in `results/run_*.txt`.

| Program | Default suite coverage |
| --- | --- |
| `check_cnf_arithmetic.py` | Carry-scan weighted sums and population counters, through 7 input bits. |
| `check_cnf_reference.py` | Gate relations and random-CNF truth tables; arithmetic cases 0–11, each run with both the carry-scan and the whole-word weighted-sum implementations; six-vertex graph masks 30000–30031. |
| `check_cnf_layers.py` | Every five-vertex undirected graph, exact weighted cut multiplicities and HC-layer parity. |
| `check_cnf_witness.py` | All 64 binary isolation-weight vectors on K4, both feasibility and lexicographic optimization. Weight range 2 is a finite logic test, not an experiment using the standard range at least twice the universe size. |
| `check_cnf_paths.py` | Every five-vertex undirected graph for prescribed paths; four-vertex directed cycles on masks 2048–2559 and directed paths on masks 3584–4095, retaining graphs with at most eight arcs. |
| `check_cnf_objects.py` | Every four-vertex graph for Steiner, marked forests, connected covers and domination. |
| `check_cnf_weighted_objects.py` | Four seeded five-vertex instances per problem, costs, exact cut counts, and object-bit witness recovery. |
| `check_cnf_failures.py` | Missing terminal selection, missing root pin, unguarded edges, omitted marker isolation, incorrect forest root pins, and a feasible but suboptimal optimization output. |
| `check_cnf_steiner.py` | Four-vertex digraph masks 0–511 and 3584–4095, each with seven nonempty terminal sets; terminal-selection units included. |
| `check_cnf_modular.py` | K6 modulo four: every partial-matching support up to the required cutoff, coefficients computed directly by subset sums, and exact unsigned CNF queries. |
| `check_cnf_boundaries.py` | Bipartite and disconnected examples, C8 and C9, small moduli, even-order division, and tight raw support cutoffs. The optional twelve-vertex color-family calculation is excluded from the default suite. |
| `check_cnf_large.py` | Actual CNF unique-extension tests for 253 and 254 inputs with 32-bit coefficients, crossing a default radix boundary. |
| `check_cnf_scaling.py` | Gate accounting through 4096 inputs and sparse wheels with high maximum degree. Cases beyond 256 inputs count gates without storing or solving the complete CNF. |

The 23 new invocations and the 24 preceding checks run serially. Individual elapsed times are in `results/manifest.json`; the runner enforces a 900-second limit per child. The baseline, layers, and residues batches each have their own outer timeout. The two slowest families (modular supports and fixed-input CNF checks) run in the last batch. To run one addition separately from `anc/`, use the relative command recorded in the manifest under the same niceness and memory limit; create `results/` first. Larger graph ranges can be split using the scripts' start/stop arguments. Only the ranges actually run above are claimed here; no earlier computation record is distributed as a fresh run. Small examples test exact reductions and do not establish the asymptotic size or success-probability theorems.

Recorded child-time totals for the baseline, layers, and residues batches are 212.6 s, 233.9 s, 815.4 s, respectively. The slowest individual checks are the K6 support expansion (404.0 s) and the fixed-input checks at 253 inputs (267.6 s) and 254 inputs (121.1 s). These are machine-dependent timing observations; all three batches fit their separate 900-second limits on these measurements.
