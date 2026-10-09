import ReflectedLiouville.CharacterAlgebra
import ReflectedLiouville.LiouvilleMean
import ReflectedLiouville.AnalyticTargets

set_option autoImplicit false
open Filter
open scoped BigOperators
open OAI.TwoPointCorrelations

namespace ReflectedLiouville

lemma character_prime_re_ge_neg_one {q : ℕ} (χ : DirichletCharacter ℂ q) (p : ℕ) :
    -1 ≤ (χ (p : ZMod q)).re :=
  (abs_le.mp ((Complex.abs_re_le_norm _).trans (χ.norm_le_one _))).1

lemma principal_prime_re_nonneg {q : ℕ} (p : ℕ) :
    0 ≤ ((1 : DirichletCharacter ℂ q) (p : ZMod q)).re := by
  by_cases h : IsUnit (p : ZMod q)
  · rw [MulChar.one_apply h]
    norm_num
  · rw [MulChar.map_nonunit _ h]
    norm_num

lemma split_prime_character_sum {q : ℕ} (χ : DirichletCharacter ℂ q) (X Y : ℝ) :
    (∑ p ∈ primesUpTo ⌊X⌋₊, (χ (p : ZMod q)).re / p) =
      (∑ p ∈ (primesUpTo ⌊X⌋₊).filter (fun p : ℕ => (p : ℝ) ≤ Y), (χ (p : ZMod q)).re / p) +
      (∑ p ∈ (primesUpTo ⌊X⌋₊).filter (fun p : ℕ => Y < (p : ℝ)), (χ (p : ZMod q)).re / p) := by
  classical
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases h : (p : ℝ) ≤ Y
  · have hnot : ¬ Y < (p : ℝ) := not_lt.mpr h
    simp [h, hnot]
  · have hlt : Y < (p : ℝ) := lt_of_not_ge h
    simp [h, hlt]

lemma small_prime_character_sum_lower {q : ℕ} (χ : DirichletCharacter ℂ q) (X Y : ℝ) :
    -(∑ p ∈ (primesUpTo ⌊X⌋₊).filter (fun p : ℕ => (p : ℝ) ≤ Y), (1 : ℝ) / p) ≤
      ∑ p ∈ (primesUpTo ⌊X⌋₊).filter (fun p : ℕ => (p : ℝ) ≤ Y), (χ (p : ZMod q)).re / p := by
  classical
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_le_sum
  intro p hp
  have h := div_le_div_of_nonneg_right (character_prime_re_ge_neg_one χ p) (Nat.cast_nonneg p)
  simpa only [neg_div] using h

lemma small_prime_reciprocal_sum_le (X Y : ℝ) (hY : 0 ≤ Y) :
    (∑ p ∈ (primesUpTo ⌊X⌋₊).filter (fun p : ℕ => (p : ℝ) ≤ Y), (1 : ℝ) / p) ≤
      ∑ p ∈ sievePrimesUpTo Y, (1 : ℝ) / p := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    obtain ⟨hpX, hpY⟩ := Finset.mem_filter.mp hp
    have hprime := (Finset.mem_filter.mp hpX).2
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_Iic.mpr ((Nat.le_floor_iff hY).mpr hpY), hprime⟩
  · intro p hp hnot
    positivity

/-- Exact finite bookkeeping isolates the analytic tail estimate. -/
lemma character_distance_lower_from_tail {q : ℕ} (χ : DirichletCharacter ℂ q)
    (X Y A B : ℝ) (hY : 0 ≤ Y)
    (hfull : Real.log (Real.log X) - A ≤ ∑ p ∈ sievePrimesUpTo X, (1 : ℝ) / p)
    (hlow : (∑ p ∈ sievePrimesUpTo Y, (1 : ℝ) / p) ≤ Real.log (Real.log Y) + A)
    (htail : -B ≤ ∑ p ∈ (primesUpTo ⌊X⌋₊).filter (fun p : ℕ => Y < (p : ℝ)),
      (χ (p : ZMod q)).re / p) :
    Real.log (Real.log X) - Real.log (Real.log Y) - 2 * A - B ≤
      squaredDistance (fun n => liouville n * χ (n : ZMod q)) (modulusOneTwist 0) ⌊X⌋₊ := by
  rw [liouville_character_untwisted_distance, primesUpTo_floor_eq_sievePrimesUpTo]
  have hsplit := split_prime_character_sum χ X Y
  have hsmall := small_prime_character_sum_lower χ X Y
  have hrecip := small_prime_reciprocal_sum_le X Y hY
  rw [primesUpTo_floor_eq_sievePrimesUpTo] at hsplit hsmall hrecip htail
  linarith

#print axioms character_distance_lower_from_tail

end ReflectedLiouville
