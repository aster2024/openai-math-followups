import ReflectedLiouville.ReflectedTupleProfiles

set_option autoImplicit false
open scoped BigOperators Classical
open OAI.TwoPointCorrelations Finset
namespace ReflectedLiouville

lemma reflected_tuple_nonraw_prefix_normalized {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j k, k ≠ j → Disjoint (P j) (P k))
    (q N : ℕ) (T : ℝ) (hcop : ∀ j, ∀ p ∈ P j, q.Coprime p)
    (eligible : ℕ → ℕ → Prop) :
    (positivePrefix (reflectedTupleCenteredProfile P q N eligible) ⌊T⌋₊ -
      positivePrefix (reflectedTuplePartialProfile P ∅ q N eligible) ⌊T⌋₊) / (T : ℂ) =
      ∑ I ∈ (Finset.univ : Finset (Fin J)).powerset.filter Finset.Nonempty,
        (-1 : ℂ) ^ I.card * (positivePrefix (reflectedTuplePartialProfile P I q N eligible) ⌊T⌋₊ / (T : ℂ)) := by
  rw [reflected_tuple_nonraw_prefix P hprime hdisjoint q N ⌊T⌋₊ hcop eligible,
    Finset.sum_div]
  apply Finset.sum_congr rfl
  intro I hI
  ring

lemma reflected_partial_centering_sum_bound {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j k, k ≠ j → Disjoint (P j) (P k))
    (hmass : ∀ j, 1 ≤ primeHarmonicMass (P j))
    (Q : Finset ℕ) (weight : ℕ → ℝ) (hweight : ∀ q ∈ Q, 0 ≤ weight q)
    (hcop : ∀ q ∈ Q, ∀ j, ∀ p ∈ P j, q.Coprime p)
    (eligible : ℕ → ℕ → Prop) (N : ℕ) (T : ℝ)
    (E : ℝ) (hE : 0 ≤ E)
    (hbound : ∀ q ∈ Q, ∀ I ∈ (univ : Finset (Fin J)).powerset.filter Finset.Nonempty,
      ‖positivePrefix (reflectedTuplePartialProfile P I q N eligible) ⌊T⌋₊ / (T : ℂ)‖ ≤
        E * ((1 / (q : ℝ)) * ∏ j : {j // j ∉ I}, primeHarmonicMass (P j))) :
    ‖∑ q ∈ Q, (weight q : ℂ) *
      ((positivePrefix (reflectedTupleCenteredProfile P q N eligible) ⌊T⌋₊ -
        positivePrefix (reflectedTuplePartialProfile P ∅ q N eligible) ⌊T⌋₊) / (T : ℂ))‖ ≤
      E * (2 : ℝ) ^ J * (∑ q ∈ Q, weight q / (q : ℝ)) *
        ∏ j, primeHarmonicMass (P j) := by
  let V := ∏ j, primeHarmonicMass (P j)
  have hV : 0 ≤ V := prod_nonneg fun j _ => zero_le_one.trans (hmass j)
  have hc : (((univ : Finset (Fin J)).powerset.filter Finset.Nonempty).card : ℝ) ≤
      (2 : ℝ) ^ J := by
    have hn := card_le_card (filter_subset (s := (univ : Finset (Fin J)).powerset)
      (p := Finset.Nonempty))
    simpa only [card_powerset, card_univ, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat] using
      (show (((univ : Finset (Fin J)).powerset.filter Finset.Nonempty).card : ℝ) ≤
        ((univ : Finset (Fin J)).powerset.card : ℝ) by exact_mod_cast hn)
  calc
    _ ≤ ∑ q ∈ Q, ‖(weight q : ℂ) *
        ((positivePrefix (reflectedTupleCenteredProfile P q N eligible) ⌊T⌋₊ -
          positivePrefix (reflectedTuplePartialProfile P ∅ q N eligible) ⌊T⌋₊) / (T : ℂ))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ q ∈ Q, weight q * ((2 : ℝ) ^ J * (E * (1 / (q : ℝ)) * V)) := by
      apply sum_le_sum
      intro q hq
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hweight q hq),
        reflected_tuple_nonraw_prefix_normalized P hprime hdisjoint q N T (hcop q hq)]
      apply mul_le_mul_of_nonneg_left _ (hweight q hq)
      calc
        _ ≤ ∑ I ∈ (univ : Finset (Fin J)).powerset.filter Finset.Nonempty,
            ‖(-1 : ℂ) ^ I.card *
              (positivePrefix (reflectedTuplePartialProfile P I q N eligible) ⌊T⌋₊ / (T : ℂ))‖ :=
          norm_sum_le _ _
        _ ≤ ∑ _I ∈ (univ : Finset (Fin J)).powerset.filter Finset.Nonempty,
            E * (1 / (q : ℝ)) * V := by
          apply sum_le_sum
          intro I hI
          simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
          apply (hbound q hq I hI).trans
          have hv := complement_product_le (fun j => primeHarmonicMass (P j)) hmass I
          dsimp only [V]
          calc
            _ = (E * (1 / (q : ℝ))) * ∏ j : {j // j ∉ I}, primeHarmonicMass (P j) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left hv (by positivity)
        _ ≤ (2 : ℝ) ^ J * (E * (1 / (q : ℝ)) * V) := by
          simp only [sum_const, nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by
      rw [mul_sum, sum_mul]
      apply sum_congr rfl
      intro q _
      dsimp only [V]
      ring


#print axioms reflected_partial_centering_sum_bound
end ReflectedLiouville
