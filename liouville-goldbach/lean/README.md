# Lean 4 formalization

This directory contains a Lean 4 formalization of Theorem 1.1 of the paper, including the exponent 10⁻²⁰⁰, from the
OpenAI library and one published analytic statement.

## Statement

`MRTRepulsion/Main.lean` proves

```lean
theorem paper_theorem_1_1_one_hypothesis
    (h_KMT : ReflectedLiouville.KMTInput) : ReflectedLiouville.PaperMainStatement
```

and `VerificationOneHypothesis.lean` restates it with every definition unfolded:

```lean
theorem paper_theorem_1_1_one_hypothesis_literal
    (h_KMT : ReflectedLiouville.KMTInput) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      (|∑ n ∈ Finset.Ico 1 N, (ArithmeticFunction.liouville n : ℝ) *
          (ArithmeticFunction.liouville (N-n) : ℝ)| ≤
        C*(N : ℝ)/Real.rpow (Real.log (N : ℝ)) (1/(10 : ℝ)^(200 : ℕ))) ∧
      (∀ e₁ e₂ : ℤ, (e₁ = -1 ∨ e₁ = 1) → (e₂ = -1 ∨ e₂ = 1) →
        |((((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)).filter (fun ab =>
            ab.1+ab.2 = N ∧ ArithmeticFunction.liouville ab.1 = e₁ ∧
              ArithmeticFunction.liouville ab.2 = e₂)).card : ℝ) - (N : ℝ)/4| ≤
          C*(N : ℝ)/Real.rpow (Real.log (N : ℝ)) (1/(10 : ℝ)^(200 : ℕ)))
```

Here `ArithmeticFunction.liouville` is Mathlib's Liouville function: the first bound is the correlation estimate and
the second is the count of each of the four ordered sign patterns (λ(a), λ(b)), a + b = N.

`ReflectedLiouville/Main.lean` and `Verification.lean` contain the same statements with an unspecified positive
exponent c (`reflected_liouville_log_saving`, `reflected_liouville_sign_patterns`,
`reflected_liouville_main_and_sign_patterns`). The files `ReflectedLiouville/Explicit*.lean` prove the comparison
estimates of the library again with fixed exponents, obtain the bound 10⁶ for the common comparison exponent, as in
Lemma 3.5 of the paper, and assemble the explicit theorem.

## Hypothesis

The argument of the theorem is a proposition defined in `ReflectedLiouville/PublishedInputs.lean`. It is a
hypothesis of the theorem, not an axiom, and it is not proved here.

`KMTInput` has one field, `KMTRealProgressionVarianceInput`: the variance estimate of Corollary 1.6 of
Klurman–Mangerel–Teräväinen (arXiv:1909.12280v5) for real-valued 1-bounded multiplicative functions over the unit
residue classes of a typical modulus q. The statements of Theorem 1.5 and Corollary 1.6 assert the existence of a
set of good moduli; the hypothesis uses the explicit set (a zero-free box for the L-functions of characters of
large conductor) of Proposition 9.4, with the substitution of §9.2 and the proof of Corollary 1.6. It is stated on a
restricted range of parameters, each restriction corresponding to a step of the printed proof: the accuracy
threshold (log X)^(−1/50) of Corollary 8.4 and Lemma 8.2, the condition q·(H/Q)^(ε^1.1/100) ≤ Q used in the first
mean-value estimate of §9.3, and log(H/Q) ≤ (log X)^(2/5), under which the interval inequalities (52) are checked
in Section 2 of the paper.

The second analytic input of the paper, Lemma C.1 of Matomäki–Radziwiłł–Tao (arXiv:1503.05121v3) for the trivial
character, is the proposition `MRTRealTwistRepulsionInput` of the same file. It is proved without hypotheses in
`MRTRepulsion/` (`mrt_real_twist_repulsion`) from the library's growth bound for the zeta function and its prime number
theorem with phases. The theorems `paper_theorem_1_1_explicit` (`ReflectedLiouville/ExplicitMain.lean`) and
`reflected_liouville_log_saving` (`ReflectedLiouville/Main.lean`) take both propositions as arguments.

Everything else is proved from Mathlib and from the OpenAI library
([github.com/openai/math](https://github.com/openai/math) at commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`), in
particular from its theorems on two-point correlations (family 007) and from
`DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re` (family 003). The proofs contain no `sorry` and
declare no axiom. For `paper_theorem_1_1_one_hypothesis`, its unfolded statement, `mrt_real_twist_repulsion`,
`paper_theorem_1_1_explicit` and the three theorems of `ReflectedLiouville/Main.lean`, `#print axioms` reports

```text
[propext, Classical.choice, Quot.sound]
```

## What is not formalized

- The published statement listed above.
- Numerical values of the constants C and N₀.
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

compiles the modules in the import closure of `VerificationOneHypothesis.lean` in dependency order with `lean -o` and
prints the axiom reports (`--target VerificationExplicit` and `--target Verification` build the versions with two
hypotheses). The formalization consists of 239 files (about 19,200 lines): `ReflectedLiouville/` (213 files),
`RealCharacterTail/` (16 files), `MRTRepulsion/` (7 files) and three verification files. `SHA256SUMS` lists the files.
