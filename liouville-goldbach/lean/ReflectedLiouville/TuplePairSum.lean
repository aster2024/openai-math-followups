import ReflectedLiouville.KeptRowPairing

set_option autoImplicit false
open scoped BigOperators Classical
open OAI.TwoPointCorrelations

namespace ReflectedLiouville

lemma tuple_pair_sum {J : ℕ} {α : Type*} [AddCommMonoid α]
    (P : Fin J → Finset ℕ) (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j k, k ≠ j → Disjoint (P j) (P k))
    (Q : Finset ℕ) (I : Finset (ℕ × ℕ))
    (hsub : I ⊆ primeTupleDivisors P ×ˢ Q) (F : ℕ × ℕ → α) :
    (∑ x : (j : Fin J) → P j, ∑ q ∈ Q,
      if (∏ j, (x j).val, q) ∈ I then F (∏ j, (x j).val, q) else 0) = ∑ dq ∈ I, F dq := by
  have htuple : (∑ d ∈ primeTupleDivisors P, ∑ q ∈ Q, if (d,q) ∈ I then F (d,q) else 0) =
      ∑ x : (j : Fin J) → P j, ∑ q ∈ Q,
        if (∏ j, (x j).val, q) ∈ I then F (∏ j, (x j).val, q) else 0 := by
    rw [primeTupleDivisors, Finset.sum_image]
    intro x hx y hy he
    exact primeTuple_injective hprime hdisjoint he
  rw [← htuple]
  have hprod : (∑ dq ∈ primeTupleDivisors P ×ˢ Q, if dq ∈ I then F dq else 0) =
      ∑ d ∈ primeTupleDivisors P, ∑ q ∈ Q, if (d,q) ∈ I then F (d,q) else 0 :=
    Finset.sum_product _ _ _
  rw [← hprod, ← Finset.sum_filter]
  have he : ((primeTupleDivisors P) ×ˢ Q).filter (fun dq => dq ∈ I) = I := by
    ext dq
    simp only [Finset.mem_filter]
    exact ⟨fun hh => hh.2, fun hh => ⟨hsub hh, hh⟩⟩
  rw [he]

#print axioms tuple_pair_sum
end ReflectedLiouville
