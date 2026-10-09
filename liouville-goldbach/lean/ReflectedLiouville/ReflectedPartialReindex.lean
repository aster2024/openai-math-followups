import ReflectedLiouville.ReflectedTupleProfiles
import ReflectedLiouville.ComplexDilation
import OAI.NumberTheory.TwoPoint.Bounds.ComplexPartialProfiles

set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped BigOperators Classical
open OAI.TwoPointCorrelations Finset
namespace ReflectedLiouville

noncomputable def reflectedPartialAtom (N u : ℕ) (Z : Finset ℕ) (n : ℕ) : ℂ :=
  natDivisibilityIndicator u n * ∑ z ∈ Z, (z : ℂ)⁻¹ *
    (liouville n * liouville (N * (u * z) - n))

lemma reflected_tuple_partial_reindex {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j k, k ≠ j → Disjoint (P j) (P k))
    (I : Finset (Fin J)) (q : ℕ) (eligible : ℕ → ℕ → Prop)
    (N n : ℕ) :
    reflectedTuplePartialProfile P I q N eligible n =
      ∑ y : (j : {j // j ∉ I}) → P j,
        reflectedPartialAtom N (q * ∏ j : {j // j ∉ I}, (y j).val)
          ((primeTupleSlice P I).filter (fun z => eligible ((∏ j : {j // j ∉ I}, (y j).val) * z) q)) n := by
  let H : ℕ → ℕ → ℂ := fun t z =>
    if eligible (t * z) q then (z : ℂ)⁻¹ *
      (natDivisibilityIndicator (q * t) n *
        (liouville n * liouville (N * (q * t * z) - n))) else 0
  have hs := primeTupleSlice_split_sum P I hprime hdisjoint H
  have hleft : reflectedTuplePartialProfile P I q N eligible n =
      ∑ x : (j : Fin J) → P j,
        H (∏ j : {j // j ∉ I}, (x j).val) (∏ i : I, (x i).val) := by
    apply sum_congr rfl
    intro x _
    have he : (∏ j : {j // j ∉ I}, (x j).val) * (∏ i : I, (x i).val) =
        ∏ j, (x j).val := by
      have hI := prod_coe_sort I (fun j : Fin J => (x j).val)
      have hIc := (prod_subtype (p := fun j : Fin J => j ∉ I) (F := inferInstance) (univ \ I) (by simp) (fun j : Fin J => (x j).val)).symm
      rw [hI, hIc, ← prod_union sdiff_disjoint, sdiff_union_of_subset (subset_univ I)]
    dsimp only [H]
    simp only [mul_assoc, he, one_div]
  rw [hleft, hs]
  apply sum_congr rfl
  intro y _
  rw [reflectedPartialAtom, mul_sum, sum_filter]
  apply sum_congr rfl
  intro z _
  dsimp only [H]
  split_ifs
  · simp only [mul_assoc]
    ring
  · simp

lemma reflected_partial_atom_prefix (N u : ℕ) (Z : Finset ℕ) (T : ℝ) (hu : 0 < u) :
    positivePrefix (reflectedPartialAtom N u Z) ⌊T⌋₊ =
      ∑ z ∈ Z, (z : ℂ)⁻¹ * ∑ m ∈ Icc 1 ⌊T / u⌋₊,
        liouville m * liouville (N * z - m) := by
  simp only [positivePrefix_eq_Icc, reflectedPartialAtom, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro z hz
  rw [← mul_sum]
  have hp := reflected_mean_atom_dilation (N * z) u hu T
  have he : N * (u * z) = u * (N * z) := by ring
  rw [he]
  rw [← hp, mul_sum]
  apply sum_congr rfl
  intro x hx
  ring

lemma reflected_tuple_partial_prefix_reindex {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j k, k ≠ j → Disjoint (P j) (P k))
    (I : Finset (Fin J)) (q N : ℕ) (hq : 0 < q) (T : ℝ) (eligible : ℕ → ℕ → Prop) :
    positivePrefix (reflectedTuplePartialProfile P I q N eligible) ⌊T⌋₊ =
      ∑ y : (j : {j // j ∉ I}) → P j,
        ∑ z ∈ (primeTupleSlice P I).filter (fun z => eligible ((∏ j : {j // j ∉ I}, (y j).val) * z) q),
          (z : ℂ)⁻¹ * ∑ m ∈ Icc 1 ⌊T / ((q * ∏ j : {j // j ∉ I}, (y j).val : ℕ) : ℝ)⌋₊,
            liouville m * liouville (N * z - m) := by
  simp only [positivePrefix, reflected_tuple_partial_reindex P hprime hdisjoint]
  rw [sum_comm]
  apply sum_congr rfl
  intro y hy
  exact reflected_partial_atom_prefix N _ _ T
    (Nat.mul_pos hq (prod_pos fun j _ => (hprime j _ (y j).property).pos))

#print axioms reflected_tuple_partial_prefix_reindex
end ReflectedLiouville
