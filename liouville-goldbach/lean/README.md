# Lean 4 formalization

This directory contains a Lean 4 formalization of the deduction of Theorem 1.1 of the paper, with an unspecified
positive exponent in place of 10⁻²⁰⁰, from the OpenAI library and two published analytic statements.

## Statement

`ReflectedLiouville/Main.lean` proves

```lean
theorem reflected_liouville_log_saving
    (h_KMT : KMTInput) (h_MRT : MRTRealTwistRepulsionInput) : ReflectedLogSaving
```

and `Verification.lean` restates it with every definition unfolded:

```lean
theorem reflected_liouville_log_saving_literal
    (h_KMT : ReflectedLiouville.KMTInput)
    (h_MRT : ReflectedLiouville.MRTRealTwistRepulsionInput) :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, 3 ≤ N₀ ∧
      ∀ N : ℕ, N₀ ≤ N →
        |∑ n ∈ Finset.Ico 1 N, (ArithmeticFunction.liouville n : ℝ) *
          (ArithmeticFunction.liouville (N-n) : ℝ)| ≤
            C*(N : ℝ)/Real.rpow (Real.log (N : ℝ)) c
```

Here `ArithmeticFunction.liouville` is Mathlib's Liouville function. The same file `Main.lean` proves
`reflected_liouville_sign_patterns` (each of the four ordered sign patterns (λ(a), λ(b)), a + b = N, occurs
N/4 + O(N/(log N)^c) times, with the count defined over ordered pairs of positive integers) and
`reflected_liouville_main_and_sign_patterns` (both statements with the same c, C and N₀).

## Hypotheses

The two arguments of the theorem are propositions defined in `ReflectedLiouville/PublishedInputs.lean`. They are
hypotheses of the theorem, not axioms, and they are not proved here.

1. `KMTInput` has one field, `KMTRealProgressionVarianceInput`: the variance estimate of Corollary 1.6 of
   Klurman–Mangerel–Teräväinen (arXiv:1909.12280v5) for real-valued 1-bounded multiplicative functions over the unit
   residue classes of a typical modulus q. The statements of Theorem 1.5 and Corollary 1.6 assert the existence of a
   set of good moduli; the hypothesis uses the explicit set (a zero-free box for the L-functions of characters of
   large conductor) of Proposition 9.4, with the substitution of §9.2 and the proof of Corollary 1.6. It is stated on a
   restricted range of parameters, each restriction corresponding to a step of the printed proof: the accuracy
   threshold (log X)^(−1/50) of Corollary 8.4 and Lemma 8.2, the condition q·(H/Q)^(ε^1.1/100) ≤ Q used in the first
   mean-value estimate of §9.3, and log(H/Q) ≤ (log X)^(2/5), under which the interval inequalities (52) are checked
   in Section 2 of the paper.
2. `MRTRealTwistRepulsionInput`: Lemma C.1 of Matomäki–Radziwiłł–Tao (arXiv:1503.05121v3), inequalities (C.1) and
   (C.2), for the trivial character.

Everything else is proved from Mathlib and from the OpenAI library
([github.com/openai/math](https://github.com/openai/math) at commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`), in
particular from its theorems on two-point correlations (family 007) and from
`DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re` (family 003). The proofs contain no `sorry` and
declare no axiom. For the three theorems of `Main.lean` and for the unfolded statement, `#print axioms` reports

```text
[propext, Classical.choice, Quot.sound]
```

## What is not formalized

- The explicit exponent 10⁻²⁰⁰ of Theorem 1.1. The proposition `PaperMainStatement` of
  `ReflectedLiouville/Definitions.lean` states it and is not proved: it requires a numerical upper bound for the
  comparison exponent A of the library, whose theorem asserts the existence of A. The constants C and N₀ are not
  explicit.
- The two published statements listed above.
- Part II of the paper (consequences of the 7/8 theorem for Goldbach numbers, the least prime in a progression,
  nonresidues and primitive roots).

## Differences from the written proof

- Lemma 2.2 (real character sums of λ). The paper uses a truncated Perron formula with the local expansion of L′/L
  and a zero count from Montgomery–Vaughan. The formal proof (`RealCharacterTail/`) derives the bounded prime-sum tail
  from the 7/8 zero-free half-plane by a holomorphic logarithm of L(s, χ), the Borel–Carathéodory inequality on a
  fixed strip and a smoothed Perron formula, and assumes nothing beyond the library.
- The Halász step uses the library theorem `halasz_mean_value` for completely multiplicative functions.
- The compression step uses the library's estimate for the self-adjoint graph together with an exact pairing between
  sources supported on positive and targets supported on negative physical integers
  (`ReflectedLiouville/CrossSupportPairing.lean`, `ReflectedCompression.lean`), which is what the reflected
  correlation requires. The two-layer operator bound of Proposition 5.3 is not formalized in that form.
- In Lemma 2.4 the window identity is used with the upper bound h + 1 for the sum of coefficient differences
  (`ReflectedLiouville/Windows.lean`).

## Building

Requirements: Lean 4.34.1 and a checkout of github.com/openai/math at the commit above in which the modules listed
in `oai_imports.txt` have been built (`lake build` in its `lean/` directory with those module names). Then

```bash
python3 build.py --oai /path/to/openai-math/lean --lean /path/to/lean --jobs 3
```

compiles the 201 modules in the import closure of `Verification.lean` in dependency order with `lean -o` and prints
the axiom reports. The formalization consists of 212 files (about 14,300 lines): `ReflectedLiouville/` (195 files),
`RealCharacterTail/` (16 files) and `Verification.lean`. `SHA256SUMS` lists the files.
