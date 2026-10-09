import RealCharacterTail.Main

set_option autoImplicit false
open scoped BigOperators

namespace RealCharacterTail.Verification

/-- Independent copy of the main project's predicate. -/
def RealCharacter {q : ℕ} (χ : DirichletCharacter ℂ q) : Prop :=
  ∀ a : ZMod q, (χ a).im = 0

/-- Independent copy of the main project's exact target, without importing it. -/
def RealCharacterPrimeTailBound : Prop :=
  ∃ C X₀ : ℝ, 0 < C ∧ 100 ≤ X₀ ∧ ∀ X : ℝ, X₀ ≤ X →
    ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ X →
      ∀ χ : DirichletCharacter ℂ q, RealCharacter χ → χ ≠ 1 →
        |∑ p ∈ (OAI.TwoPointCorrelations.primesUpTo ⌊X⌋₊).filter
          (fun p : ℕ => (Real.log X) ^ (64 : ℕ) < (p : ℝ)), (χ (p : ZMod q)).re / p| ≤ C

theorem closes_analytic_target : RealCharacterPrimeTailBound := by
  exact RealCharacterTail.real_character_prime_tail

end RealCharacterTail.Verification

#print RealCharacterTail.real_character_prime_tail
#print axioms RealCharacterTail.real_character_prime_tail
#print axioms RealCharacterTail.Verification.closes_analytic_target
