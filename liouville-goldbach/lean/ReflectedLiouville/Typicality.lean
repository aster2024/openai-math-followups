import ReflectedLiouville.PublishedInputs
import Mathlib.Tactic

set_option autoImplicit false
open OAI.TwoPointCorrelations

namespace ReflectedLiouville

lemma primesUpTo_mono {n m : ℕ} (hnm : n ≤ m) : primesUpTo n ⊆ primesUpTo m := by
  intro p hp
  obtain ⟨hp, hprime⟩ := Finset.mem_filter.mp hp
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_range.mpr ((Finset.mem_range.mp hp).trans_le (by omega)), hprime⟩

/-- A sufficient finite prime-counting test for the exact published typicality. -/
lemma kmt_typical_of_prime_count (q : ℕ) [NeZero q] (y : ℝ)
    (hcount : 100 * q.primeFactors.card ≤ (primesUpTo ⌊y⌋₊).card) : KMTTypical q y := by
  intro z hyz
  have hsub : (primesUpTo ⌊z⌋₊).filter (fun p => p ∣ q) ⊆ q.primeFactors := by
    intro p hp
    obtain ⟨hp, hdiv⟩ := Finset.mem_filter.mp hp
    have hprime := (Finset.mem_filter.mp hp).2
    exact Nat.mem_primeFactors.mpr ⟨hprime, hdiv, NeZero.ne q⟩
  have hfactor := Finset.card_le_card hsub
  have hπ := Finset.card_le_card (primesUpTo_mono (Nat.floor_mono hyz))
  have hfactor' :
      (((primesUpTo ⌊z⌋₊).filter (fun p => p ∣ q)).card : ℝ) ≤ q.primeFactors.card := by
    exact_mod_cast hfactor
  have hπ' : ((primesUpTo ⌊y⌋₊).card : ℝ) ≤ (primesUpTo ⌊z⌋₊).card := by exact_mod_cast hπ
  have hcount' : 100 * (q.primeFactors.card : ℝ) ≤ (primesUpTo ⌊y⌋₊).card := by exact_mod_cast hcount
  linarith

#check Nat.prod_primeFactors_dvd
lemma prime_factor_count_le_log (q : ℕ) [NeZero q] :
    (q.primeFactors.card : ℝ) ≤ Real.log (q : ℝ) / Real.log 2 := by
  have hq : 0 < q := NeZero.pos q
  have hprod : 2 ^ q.primeFactors.card ≤ q := by
    calc
      _ = ∏ _p ∈ q.primeFactors, (2 : ℕ) := by simp
      _ ≤ ∏ p ∈ q.primeFactors, p := by
        apply Finset.prod_le_prod
        intro p hp
        exact (Nat.mem_primeFactors.mp hp).1.two_le
      _ ≤ _ := Nat.le_of_dvd hq (Nat.prod_primeFactors_dvd q)
  have hprodr : (2 : ℝ) ^ q.primeFactors.card ≤ q := by exact_mod_cast hprod
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ q.primeFactors.card) hprodr
  rw [Real.log_pow] at hlog
  exact (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr hlog

#print axioms kmt_typical_of_prime_count
#print axioms prime_factor_count_le_log

end ReflectedLiouville
