import ReflectedLiouville.Typicality
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

set_option autoImplicit false
open scoped BigOperators

namespace ReflectedLiouville

lemma totient_ratio_product (q : ℕ) [NeZero q] :
    (q : ℝ) / q.totient = ∏ p ∈ q.primeFactors, (p : ℝ) / ((p : ℝ) - 1) := by
  have hφ : (q.totient : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  have hprime (p : ℕ) (hp : p ∈ q.primeFactors) : p.Prime := (Nat.mem_primeFactors.mp hp).1
  have hden : (∏ p ∈ q.primeFactors, ((p : ℝ) - 1)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hprime p hp).two_le
    linarith
  have hpred : (∏ p ∈ q.primeFactors, ((p - 1 : ℕ) : ℝ)) =
      ∏ p ∈ q.primeFactors, ((p : ℝ) - 1) := by
    apply Finset.prod_congr rfl
    intro p hp
    rw [Nat.cast_sub (hprime p hp).one_le, Nat.cast_one]
  have heq := congrArg (fun n : ℕ => (n : ℝ)) (Nat.totient_mul_prod_primeFactors q)
  simp only [Nat.cast_mul, Nat.cast_prod] at heq
  rw [hpred] at heq
  rw [Finset.prod_div_distrib]
  apply (div_eq_div_iff hφ hden).mpr
  simpa only [mul_comm] using heq.symm

lemma prime_totient_log_cost (p : ℕ) (hp : p.Prime) :
    Real.log ((p : ℝ) / ((p : ℝ) - 1)) ≤ 2 / (p : ℝ) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hpp : (0 : ℝ) < p := by linarith
  have hpm : 0 < (p : ℝ) - 1 := by linarith
  have hlog := Real.log_le_sub_one_of_pos (div_pos hpp hpm)
  have hid : (p : ℝ) / ((p : ℝ) - 1) - 1 = 1 / ((p : ℝ) - 1) := by field_simp; ring
  rw [hid] at hlog
  apply hlog.trans
  exact (div_le_div_iff₀ hpm hpp).mpr (by nlinarith)

/-- The elementary product bound needed to absorb the real-character main term. -/
lemma log_totient_ratio_le (q : ℕ) [NeZero q] :
    Real.log ((q : ℝ) / q.totient) ≤ 2 * ∑ p ∈ q.primeFactors, (1 : ℝ) / p := by
  rw [totient_ratio_product]
  have hpos (p : ℕ) (hp : p ∈ q.primeFactors) : 0 < (p : ℝ) / ((p : ℝ) - 1) := by
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.mem_primeFactors.mp hp).1.two_le
    exact div_pos (by linarith) (by linarith)
  rw [Real.log_prod (fun p hp => (hpos p hp).ne')]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  simpa only [mul_one_div] using prime_totient_log_cost p (Nat.mem_primeFactors.mp hp).1

#print axioms log_totient_ratio_le

end ReflectedLiouville
