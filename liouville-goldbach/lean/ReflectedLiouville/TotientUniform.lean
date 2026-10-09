import ReflectedLiouville.TotientRatio
import OAI.NumberTheory.TwoPointCorrelations.FinalMain

set_option autoImplicit false
open Filter
open scoped BigOperators
open OAI.TwoPointCorrelations

namespace ReflectedLiouville

lemma prime_factor_reciprocal_split (q : ℕ) (Y : ℝ) :
    (∑ p ∈ q.primeFactors, (1 : ℝ) / p) =
      (∑ p ∈ q.primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ Y), (1 : ℝ) / p) +
      (∑ p ∈ q.primeFactors.filter (fun p : ℕ => Y < (p : ℝ)), (1 : ℝ) / p) := by
  classical
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases h : (p : ℝ) ≤ Y
  · simp [h, not_lt.mpr h]
  · simp [h, lt_of_not_ge h]

lemma small_prime_factors_reciprocal_le (q : ℕ) (Y : ℝ) (hY : 0 ≤ Y) :
    (∑ p ∈ q.primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ Y), (1 : ℝ) / p) ≤
      ∑ p ∈ sievePrimesUpTo Y, (1 : ℝ) / p := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    obtain ⟨hp, hle⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_Iic.mpr ((Nat.le_floor_iff hY).mpr hle),
      (Nat.mem_primeFactors.mp hp).1⟩
  · intro p hp hnot
    positivity

lemma large_prime_factors_reciprocal_le (q : ℕ) (Y : ℝ) (hY : 0 < Y) :
    (∑ p ∈ q.primeFactors.filter (fun p : ℕ => Y < (p : ℝ)), (1 : ℝ) / p) ≤
      (q.primeFactors.card : ℝ) / Y := by
  calc
    _ ≤ ∑ _p ∈ q.primeFactors.filter (fun p : ℕ => Y < (p : ℝ)), (1 : ℝ) / Y := by
      apply Finset.sum_le_sum
      intro p hp
      exact div_le_div_of_nonneg_left zero_le_one hY (Finset.mem_filter.mp hp).2.le
    _ = ((q.primeFactors.filter (fun p : ℕ => Y < (p : ℝ))).card : ℝ) / Y := by simp [div_eq_mul_inv]
    _ ≤ _ := div_le_div_of_nonneg_right (by exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)) hY.le

lemma prime_factor_reciprocal_uniform (A X : ℝ)
    (hMertens : ∀ y : ℝ, 2 ≤ y → |(∑ p ∈ sievePrimesUpTo y, (1 : ℝ) / p) - Real.log (Real.log y)| ≤ A)
    (hlog : 2 ≤ Real.log X) (q : ℕ) [NeZero q] (hqX : (q : ℝ) ≤ X) :
    (∑ p ∈ q.primeFactors, (1 : ℝ) / p) ≤
      Real.log (Real.log (Real.log X)) + A + 1 / Real.log 2 := by
  have hlogp : 0 < Real.log X := by linarith
  have hqp : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hlogqX := Real.log_le_log hqp hqX
  have hcard : (q.primeFactors.card : ℝ) ≤ Real.log X / Real.log 2 :=
    (prime_factor_count_le_log q).trans
      (div_le_div_of_nonneg_right hlogqX (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le)
  have hsmall := (small_prime_factors_reciprocal_le q (Real.log X) hlogp.le).trans
    (show (∑ p ∈ sievePrimesUpTo (Real.log X), (1 : ℝ) / p) ≤
      Real.log (Real.log (Real.log X)) + A by
      have h := (abs_le.mp (hMertens (Real.log X) hlog)).2
      linarith)
  have hlarge := (large_prime_factors_reciprocal_le q (Real.log X) hlogp).trans
    (div_le_div_of_nonneg_right hcard hlogp.le)
  have hid : (Real.log X / Real.log 2) / Real.log X = 1 / Real.log 2 := by field_simp
  rw [hid] at hlarge
  rw [prime_factor_reciprocal_split q (Real.log X)]
  linarith

/-- A deliberately weak but sufficient bound, derived from the proved Mertens
    statement. The constant is uniform in every modulus q ≤ X. -/
theorem totient_ratio_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, Real.exp 2 ≤ X →
      ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ X →
        (q : ℝ) / q.totient ≤ C * (Real.log (Real.log X)) ^ (2 : ℕ) := by
  obtain ⟨A, hA⟩ := primeReciprocalInput
  refine ⟨Real.exp (2 * (A + 1 / Real.log 2)), Real.exp_pos _, ?_⟩
  intro X hX q inst hqX
  have hlog : 2 ≤ Real.log X := by
    have h := Real.log_le_log (Real.exp_pos 2) hX
    simpa only [Real.log_exp] using h
  have hpf := prime_factor_reciprocal_uniform A X hA hlog q hqX
  have hbound : Real.log ((q : ℝ) / q.totient) ≤
      2 * Real.log (Real.log (Real.log X)) + 2 * (A + 1 / Real.log 2) := by
    have h := log_totient_ratio_le q
    linarith
  have hqp : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hll : 0 < Real.log (Real.log X) := Real.log_pos (by linarith)
  have he := Real.exp_le_exp.mpr hbound
  rw [Real.exp_log (div_pos hqp hφ)] at he
  have hid : Real.exp (2 * Real.log (Real.log (Real.log X)) + 2 * (A + 1 / Real.log 2)) =
      Real.exp (2 * (A + 1 / Real.log 2)) * (Real.log (Real.log X)) ^ (2 : ℕ) := by
    rw [show 2 * Real.log (Real.log (Real.log X)) + 2 * (A + 1 / Real.log 2) =
      2 * (A + 1 / Real.log 2) + (Real.log (Real.log (Real.log X)) + Real.log (Real.log (Real.log X))) by ring]
    rw [Real.exp_add, Real.exp_add, Real.exp_log hll]
    ring
  rwa [hid] at he

#print axioms totient_ratio_uniform

end ReflectedLiouville
