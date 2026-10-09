import ReflectedLiouville.GcdVarianceIntegral
import Mathlib.Tactic

set_option autoImplicit false

namespace ReflectedLiouville

lemma divisor_quotient_cast (q : ℕ) [NeZero q] (u : ↥q.divisors) :
    ((q / u.val : ℕ) : ℝ) = (q : ℝ) / u.val := by
  have hup : (u.val : ℝ) ≠ 0 := by exact_mod_cast (divisor_positive q u).ne'
  have hq := congrArg (fun n : ℕ => (n : ℝ)) (divisor_mul_quotient q u)
  simp only [Nat.cast_mul] at hq
  apply (eq_div_iff hup).mpr
  simpa only [mul_comm] using hq

lemma divisor_scaled_ratio (q : ℕ) [NeZero q] (u : ↥q.divisors) (H : ℝ) :
    (H / u.val) / ((q / u.val : ℕ) : ℝ) = H / q := by
  rw [divisor_quotient_cast]
  have hup : (u.val : ℝ) ≠ 0 := by exact_mod_cast (divisor_positive q u).ne'
  field_simp

lemma divisor_scale_bounds (q : ℕ) [NeZero q] (u : ↥q.divisors) (X H : ℝ)
    (hX : 0 ≤ X) (hH : 0 ≤ H) (hHX : H ≤ X) :
    H / q ≤ X / u.val ∧ X / u.val ≤ X ∧ H / u.val ≤ X / u.val := by
  have hup : (0 : ℝ) < u.val := by exact_mod_cast divisor_positive q u
  have hu₁ : (1 : ℝ) ≤ u.val := by exact_mod_cast divisor_positive q u
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have huq : (u.val : ℝ) ≤ q := by
    exact_mod_cast Nat.le_of_dvd (NeZero.pos q) (Nat.dvd_of_mem_divisors u.property)
  refine ⟨(div_le_div_of_nonneg_right hHX hq.le).trans
    (div_le_div_of_nonneg_left hX hup huq), ?_, div_le_div_of_nonneg_right hHX hup.le⟩
  exact (div_le_iff₀ hup).mpr (le_mul_of_one_le_right hX hu₁)

lemma divisor_scaled_length (q : ℕ) [NeZero q] (u : ↥q.divisors) (H : ℝ)
    (hHq : 10 * (q : ℝ) ≤ H) :
    10 * ((q / u.val : ℕ) : ℝ) ≤ H / u.val := by
  rw [divisor_quotient_cast]
  have hup : (0 : ℝ) < u.val := by exact_mod_cast divisor_positive q u
  have h := div_le_div_of_nonneg_right hHq hup.le
  simpa only [mul_div_assoc] using h

lemma divisor_scaled_exp_requirement (q : ℕ) [NeZero q] (u : ↥q.divisors) (X H ν : ℝ)
    (hν : 0 ≤ ν) (hX : 0 ≤ X) (hH : 0 ≤ H) (hHX : H ≤ X)
    (hR : 1 ≤ H / q) (hlarge : Real.exp ((Real.log X) ^ ν) ≤ H / q) :
    Real.exp ((Real.log (X / u.val)) ^ ν) ≤ (H / u.val) / ((q / u.val : ℕ) : ℝ) := by
  obtain ⟨hlo, hhi, hlength⟩ := divisor_scale_bounds q u X H hX hH hHX
  have hXp : 0 < X / u.val := by linarith
  have hX₁ : 1 ≤ X / u.val := hR.trans hlo
  have hlog := Real.log_le_log hXp hhi
  have hpow := Real.rpow_le_rpow (Real.log_nonneg hX₁) hlog hν
  rw [divisor_scaled_ratio]
  exact (Real.exp_le_exp.mpr hpow).trans hlarge

#print axioms divisor_scaled_exp_requirement

end ReflectedLiouville
