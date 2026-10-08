# Lean ancillary files

These files use Lean `leanprover/lean4:v4.34.1` (Release; kernel `5045d0056413266e57c625dcd7c365b10e377c52`). They import the OpenAI library at frozen commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, with Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612` and the dependencies pinned by that checkout.

| File | Content |
|---|---|
| `CRTTransport.lean` | `ReflectedLiouville.prohibited_scale` and `prohibited_CRT`: transport the positive-word, forward-prohibited, minimal-word and prohibited-site predicates under scaling and CRT. |
| `TwoLayerRows.lean` | `ReflectedLiouville.two_layer_localized_square`: both weighted row bounds imply the square bound for a Hermitian two-layer lift. |
| `ExplicitBudget.lean` | `ReflectedLiouville.braverman_degree_explicit_exponent` and `braverman_degree_positive_explicit_exponent`: the literal degree function has polynomial upper exponents 8457 and 8458. |
| `Interfaces.lean` | Reads the types and axioms of the named two-point declarations and checks three packaged premises by `exact`. |
| `InputStatements.lean` | Checks the Dirichlet seven-eighths type by `exact` and reads the zeta, word, matrix, residue and degree declarations. |

Build the upstream import closures `OAI.NumberTheory.TwoPointCorrelations.FinalMain` and `OAI.NumberTheory.DirichletL.Nonvanishing` using its pinned manifest. From the upstream `lean/` directory, check each ancillary file separately with `LEAN_NUM_THREADS=1` and `nice -n 19 lake env lean -DautoImplicit=false /absolute/path/to/anc/FILE.lean`.

The files provide input readback and finite lemmas. The bound on the comparison exponent, the final logarithmic saving and the reflected theorem are written deductions in the manuscript. The accepted axiom readback uses only `propext`, `Classical.choice` and `Quot.sound`.
