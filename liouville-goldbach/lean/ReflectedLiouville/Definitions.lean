import OAI.NumberTheory.TwoPoint.Basic
import OAI.NumberTheory.TwoPoint.PretentiousDistance
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.LSeries.Nonvanishing

set_option autoImplicit false
open scoped BigOperators ComplexConjugate

namespace ReflectedLiouville

/-- The existing OAI/Mathlib Liouville function, with its existing value 0 at 0. -/
noncomputable abbrev liouville : ℕ → ℂ := OAI.TwoPointCorrelations.liouville

/-- Its real value; this is a cast of Mathlib's integer arithmetic function. -/
noncomputable def liouvilleReal (n : ℕ) : ℝ := ArithmeticFunction.liouville n

/-- Positive integers strictly smaller than the total. -/
def reflectedIndices (N : ℕ) : Finset ℕ := Finset.Ico 1 N

/-- The reflected correlation, with exactly the range 1 ≤ n < N. -/
noncomputable def reflectedSum (N : ℕ) : ℝ :=
  ∑ n ∈ reflectedIndices N, liouvilleReal n * liouvilleReal (N - n)

/-- The single Liouville sum used in the sign-pattern identity. -/
noncomputable def linearSum (N : ℕ) : ℝ :=
  ∑ n ∈ reflectedIndices N, liouvilleReal n

/-- Ordered sign-pattern counts, parameterized by n ↦ (n, N − n). -/
noncomputable def signPatternCount (N : ℕ) (e₁ e₂ : ℤ) : ℕ :=
  ((reflectedIndices N).filter (fun n =>
    ArithmeticFunction.liouville n = e₁ ∧ ArithmeticFunction.liouville (N - n) = e₂)).card

/-- The literal ordered-pair version appearing in the paper. -/
noncomputable def orderedPairCount (N : ℕ) (e₁ e₂ : ℤ) : ℕ :=
  (((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)).filter (fun ab =>
    ab.1 + ab.2 = N ∧ ArithmeticFunction.liouville ab.1 = e₁ ∧
      ArithmeticFunction.liouville ab.2 = e₂)).card

def IsSign (e : ℤ) : Prop := e = -1 ∨ e = 1

/-- Stage 1 target: one absolute positive logarithmic exponent, all large totals. -/
def ReflectedLogSaving : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, 3 ≤ N₀ ∧
    ∀ N : ℕ, N₀ ≤ N →
      |reflectedSum N| ≤ C * (N : ℝ) / Real.rpow (Real.log (N : ℝ)) c

/-- Counts of all four ordered patterns, with the same absolute exponent. -/
def SignPatternLogSaving : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, 3 ≤ N₀ ∧
    ∀ N : ℕ, N₀ ≤ N → ∀ e₁ e₂ : ℤ, IsSign e₁ → IsSign e₂ →
      |(signPatternCount N e₁ e₂ : ℝ) - (N : ℝ) / 4| ≤
        C * (N : ℝ) / Real.rpow (Real.log (N : ℝ)) c

/-- Literal exponent in Theorem 1.1, retained as the second-stage target. -/
def PaperMainStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
    (|reflectedSum N| ≤
      C * (N : ℝ) / Real.rpow (Real.log (N : ℝ)) (1 / (10 : ℝ) ^ (200 : ℕ))) ∧
    (∀ e₁ e₂ : ℤ, IsSign e₁ → IsSign e₂ →
      |(orderedPairCount N e₁ e₂ : ℝ) - (N : ℝ) / 4| ≤
        C * (N : ℝ) / Real.rpow (Real.log (N : ℝ)) (1 / (10 : ℝ) ^ (200 : ℕ)))

end ReflectedLiouville
