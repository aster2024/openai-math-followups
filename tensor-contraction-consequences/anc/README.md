# Finite checks for the tensor-contraction reductions

From the directory containing this `anc/` folder, run:

```bash
nice -n 19 bash -c 'ulimit -v 8388608; timeout 900s python3 -B -I anc/run_all.py'
```

Requirements: Python 3, NumPy, a C++17 compiler named `g++`, and a POSIX environment. The runner compiles two C++ programs in a temporary directory, runs 24 checks serially, and removes the temporary executables. It enforces niceness 19, an 8 GiB address-space limit, a 900-second timeout per child, and one native thread per child. The outer timeout bounds the complete suite. No network access is needed. Each check and the runner print one summary line. Detailed outputs are written to `results/`.

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
| `c2_p2_p3_check.py` | Section 9.2 | Consistent-cut multiplicities, parity Hamiltonian-cycle layers, and marker-forest conditions. |
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
