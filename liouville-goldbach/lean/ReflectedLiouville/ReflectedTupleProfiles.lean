import ReflectedLiouville.CenterExpansion
import OAI.NumberTheory.TwoPoint.Bounds.CenteredTupleProfiles
import OAI.NumberTheory.TwoPoint.Bounds.PartialCenteringSum

set_option autoImplicit false
open scoped BigOperators Classical
open OAI.TwoPointCorrelations

namespace ReflectedLiouville

noncomputable def reflectedTupleCenteredProfile {J : ℕ} (P : Fin J → Finset ℕ)
    (q N : ℕ) (eligible : ℕ → ℕ → Prop) (n : ℕ) : ℂ :=
  ∑ x : (j : Fin J) → P j, if eligible (∏ j, (x j).val) q then
    natDivisibilityIndicator q n * (centeredTuple (∏ j, (x j).val).primeFactors (n : ℤ) : ℂ) *
      (liouville n * liouville (N * (q * ∏ j, (x j).val) - n)) else 0

noncomputable def reflectedTuplePartialProfile {J : ℕ} (P : Fin J → Finset ℕ)
    (I : Finset (Fin J)) (q N : ℕ) (eligible : ℕ → ℕ → Prop) (n : ℕ) : ℂ :=
  ∑ x : (j : Fin J) → P j, if eligible (∏ j, (x j).val) q then
    (1 / ((∏ i : I, (x i).val : ℕ) : ℂ)) *
      natDivisibilityIndicator (q * ∏ j : {j // j ∉ I}, (x j).val) n *
        (liouville n * liouville (N * (q * ∏ j, (x j).val) - n)) else 0

theorem reflected_tuple_profile_expansion {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime) (hdisjoint : ∀ j k, k ≠ j → Disjoint (P j) (P k))
    (q N : ℕ) (hcop : ∀ j, ∀ p ∈ P j, q.Coprime p) (eligible : ℕ → ℕ → Prop) (n : ℕ) :
    reflectedTupleCenteredProfile P q N eligible n =
      ∑ I ∈ (Finset.univ : Finset (Fin J)).powerset,
        (-1 : ℂ) ^ I.card * reflectedTuplePartialProfile P I q N eligible n := by
  simp only [reflectedTupleCenteredProfile, reflectedTuplePartialProfile, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases he : eligible (∏ j, (x j).val) q
  · simp only [he, ite_true]
    rw [centeredTuple_nat_eq P hprime hdisjoint]
    have hExpand := tuple_center_padding_expansion (fun j => (x j).val)
      (fun j => hprime j _ (x j).property) (selectedPrimeValues_injective x hdisjoint) q n
      (fun j => hcop j _ (x j).property)
      (liouville n * liouville (N * (q * ∏ j, (x j).val) - n))
    apply hExpand.trans
    apply Finset.sum_congr rfl
    intro I hI
    ring
  · simp only [he, ite_false, mul_zero, Finset.sum_const_zero]

theorem reflected_tuple_profile_nonraw {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime) (hdisjoint : ∀ j k, k ≠ j → Disjoint (P j) (P k))
    (q N : ℕ) (hcop : ∀ j, ∀ p ∈ P j, q.Coprime p) (eligible : ℕ → ℕ → Prop) (n : ℕ) :
    reflectedTupleCenteredProfile P q N eligible n - reflectedTuplePartialProfile P ∅ q N eligible n =
      ∑ I ∈ (Finset.univ : Finset (Fin J)).powerset.filter Finset.Nonempty,
        (-1 : ℂ) ^ I.card * reflectedTuplePartialProfile P I q N eligible n := by
  rw [reflected_tuple_profile_expansion P hprime hdisjoint q N hcop eligible n]
  let F : Finset (Fin J) → ℂ := fun I => (-1 : ℂ) ^ I.card * reflectedTuplePartialProfile P I q N eligible n
  have he : (Finset.univ : Finset (Fin J)).powerset.filter Finset.Nonempty =
      (Finset.univ : Finset (Fin J)).powerset.erase ∅ := by
    ext I
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.nonempty_iff_ne_empty]
    exact and_comm
  rw [he]
  change (∑ I ∈ (Finset.univ : Finset (Fin J)).powerset, F I) - _ =
    ∑ I ∈ (Finset.univ : Finset (Fin J)).powerset.erase ∅, F I
  rw [← Finset.sum_erase_add _ F (Finset.empty_mem_powerset _)]
  simp only [F, Finset.card_empty, pow_zero, one_mul, add_sub_cancel_right]

theorem reflected_tuple_nonraw_prefix {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime) (hdisjoint : ∀ j k, k ≠ j → Disjoint (P j) (P k))
    (q N X : ℕ) (hcop : ∀ j, ∀ p ∈ P j, q.Coprime p) (eligible : ℕ → ℕ → Prop) :
    positivePrefix (reflectedTupleCenteredProfile P q N eligible) X -
      positivePrefix (reflectedTuplePartialProfile P ∅ q N eligible) X =
      ∑ I ∈ (Finset.univ : Finset (Fin J)).powerset.filter Finset.Nonempty,
        (-1 : ℂ) ^ I.card * positivePrefix (reflectedTuplePartialProfile P I q N eligible) X := by
  have hdiff : positivePrefix (fun n => reflectedTupleCenteredProfile P q N eligible n -
      reflectedTuplePartialProfile P ∅ q N eligible n) X =
      positivePrefix (reflectedTupleCenteredProfile P q N eligible) X -
      positivePrefix (reflectedTuplePartialProfile P ∅ q N eligible) X := by
    simp only [positivePrefix, Finset.sum_sub_distrib]
  rw [← hdiff]
  simp_rw [reflected_tuple_profile_nonraw P hprime hdisjoint q N hcop eligible]
  rw [positivePrefix_sum_finite]
  apply Finset.sum_congr rfl
  intro I hI
  exact positivePrefix_const_mul _ _ _

#print axioms reflected_tuple_nonraw_prefix

end ReflectedLiouville
