import ReflectedLiouville.Algebra

set_option autoImplicit false
open scoped BigOperators

namespace ReflectedLiouville

/-- Counting by the first coordinate counts ordered pairs, for every total. -/
lemma signPatternCount_eq_orderedPairCount (N : ℕ) (e₁ e₂ : ℤ) :
    signPatternCount N e₁ e₂ = orderedPairCount N e₁ e₂ := by
  classical
  unfold signPatternCount orderedPairCount
  apply Finset.card_bij (fun n _ => (n, N - n))
  · intro n hn
    obtain ⟨hn, hvalues⟩ := Finset.mem_filter.mp hn
    have hn' : 1 ≤ n ∧ n < N := Finset.mem_Ico.mp hn
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
    exact ⟨⟨⟨hn'.1, by omega⟩, ⟨by omega, by omega⟩⟩, by omega, hvalues⟩
  · intro n hn m hm hnm
    exact congrArg Prod.fst hnm
  · rintro ⟨a, b⟩ hab
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hab
    obtain ⟨⟨⟨ha, haN⟩, ⟨hb, hbN⟩⟩, hsum, hva, hvb⟩ := hab
    have heq : N - a = b := by omega
    refine ⟨a, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_Ico.mpr ⟨ha, by omega⟩, hva, by simpa only [heq] using hvb⟩
    · simp only [heq]

#print axioms signPatternCount_eq_orderedPairCount

end ReflectedLiouville
