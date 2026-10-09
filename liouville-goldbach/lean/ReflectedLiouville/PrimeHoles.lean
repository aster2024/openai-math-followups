import ReflectedLiouville.Typicality

set_option autoImplicit false
open scoped BigOperators

namespace ReflectedLiouville

lemma prime_factor_subset_log_bound (N : ℕ) [NeZero N] (S : Finset ℕ) (H : ℝ)
    (hS : S ⊆ N.primeFactors) (hH : 1 < H) (hlo : ∀ p ∈ S, H ≤ (p : ℝ)) :
    (S.card : ℝ) * Real.log H ≤ Real.log (N : ℝ) := by
  have hprime (p : ℕ) (hp : p ∈ S) : Nat.Prime p := (Nat.mem_primeFactors.mp (hS hp)).1
  have hprod_dvd : (∏ p ∈ S, p) ∣ N :=
    (Finset.prod_dvd_prod_of_subset S N.primeFactors (fun p => p) hS).trans (Nat.prod_primeFactors_dvd N)
  have hprod_le : (∏ p ∈ S, p) ≤ N := Nat.le_of_dvd (NeZero.pos N) hprod_dvd
  have hprod_pos : (0 : ℝ) < ∏ p ∈ S, (p : ℝ) := by
    apply Finset.prod_pos
    intro p hp
    exact_mod_cast (hprime p hp).pos
  have hprod_le' : (∏ p ∈ S, (p : ℝ)) ≤ N := by
    have hcast : ((∏ p ∈ S, p : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hprod_le
    simpa only [Nat.cast_prod] using
      hcast
  have hlog := Real.log_le_log hprod_pos hprod_le'
  have hlog_prod : Real.log (∏ p ∈ S, (p : ℝ)) = ∑ p ∈ S, Real.log (p : ℝ) := by
    apply Real.log_prod
    intro p hp
    exact_mod_cast (hprime p hp).ne_zero
  rw [hlog_prod] at hlog
  calc
    _ = ∑ _p ∈ S, Real.log H := by simp
    _ ≤ ∑ p ∈ S, Real.log (p : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      exact Real.log_le_log (by linarith) (hlo p hp)
    _ ≤ _ := hlog

/-- The uniform prime-hole estimate used to delete factors of the total from
    the center bands. H need not be an integer. -/
lemma large_prime_factor_reciprocal_bound (N : ℕ) [NeZero N] (S : Finset ℕ) (H : ℝ)
    (hS : S ⊆ N.primeFactors) (hH : 1 < H) (hlo : ∀ p ∈ S, H ≤ (p : ℝ)) :
    (∑ p ∈ S, (1 : ℝ) / p) ≤ Real.log (N : ℝ) / (H * Real.log H) := by
  have hHp : 0 < H := by linarith
  have hlogH : 0 < Real.log H := Real.log_pos hH
  have hcard := prime_factor_subset_log_bound N S H hS hH hlo
  have hcard' : (S.card : ℝ) ≤ Real.log (N : ℝ) / Real.log H :=
    (le_div_iff₀ hlogH).mpr hcard
  calc
    _ ≤ ∑ _p ∈ S, (1 : ℝ) / H := by
      apply Finset.sum_le_sum
      intro p hp
      exact div_le_div_of_nonneg_left zero_le_one hHp (hlo p hp)
    _ = (S.card : ℝ) / H := by simp [div_eq_mul_inv]
    _ ≤ (Real.log (N : ℝ) / Real.log H) / H := div_le_div_of_nonneg_right hcard' hHp.le
    _ = _ := by ring

#print axioms large_prime_factor_reciprocal_bound

end ReflectedLiouville
