import ReflectedLiouville.ReflectionPoolBounds

set_option autoImplicit false
open scoped Classical
open OAI.TwoPointCorrelations

namespace ReflectedLiouville

/-- Rebase only the displacement multiplier; all numerical supplies remain. -/
noncomputable def rebasePrimeFamily {h J M : ℕ} (data : ProhibitedPrimeFamily h J M)
    (h' : ℕ) (hexcluded : ∀ p ∈ data.P, ¬ p ∣ h') : ProhibitedPrimeFamily h' J M where
  P := data.P
  Q := data.Q
  pairs := data.pairs
  primeP := data.primeP
  primeQ := data.primeQ
  disjoint := data.disjoint
  excluded := hexcluded
  tuple_squarefree := data.tuple_squarefree
  padding_squarefree := data.padding_squarefree
  tuple_card := data.tuple_card
  padding_card := data.padding_card
  tuple_pool := data.tuple_pool
  padding_pool := data.padding_pool

noncomputable def quotientPrimeFamily {h J M : ℕ} (data : ProhibitedPrimeFamily h J M) :
    ProhibitedPrimeFamily 1 J M := rebasePrimeFamily data 1
      (fun p hp hdiv => (data.primeP p hp).ne_one (Nat.dvd_one.mp hdiv))

lemma ReflectionPoolRange.rebase {h J M : ℕ} (data : ProhibitedPrimeFamily h J M)
    (P : Fin J → Finset ℕ) (L W α : ℝ) (hrange : ReflectionPoolRange data P L W α)
    (h' : ℕ) (hexcluded : ∀ p ∈ data.P, ¬ p ∣ h') :
    ReflectionPoolRange (rebasePrimeFamily data h' hexcluded) P L W α := by
  rcases hrange with ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆, h₁₇, h₁₈⟩
  exact ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆, h₁₇, h₁₈⟩

lemma ReflectionPoolRange.quotient {h J M : ℕ} (data : ProhibitedPrimeFamily h J M)
    (P : Fin J → Finset ℕ) (L W α : ℝ) (hrange : ReflectionPoolRange data P L W α) :
    ReflectionPoolRange (quotientPrimeFamily data) P L W α :=
  hrange.rebase data P L W α 1 _

#print axioms ReflectionPoolRange.quotient

end ReflectedLiouville
