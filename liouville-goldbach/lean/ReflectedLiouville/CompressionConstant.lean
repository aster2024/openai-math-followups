import ReflectedLiouville.GenericCompression

set_option autoImplicit false
open scoped Classical

namespace ReflectedLiouville

lemma compression_numeric_coefficient : (12 : ℝ) * Real.exp 151 ≤ (3 : ℝ) ^ (170 : ℕ) := by
  have he : Real.exp 151 ≤ (3 : ℝ) ^ (151 : ℕ) := by
    have hid : Real.exp 151 = (Real.exp 1) ^ (151 : ℕ) := by
      rw [← Real.exp_nat_mul]
      norm_num
    rw [hid]
    exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le 151
  have hnum : (12 : ℝ) * (3 : ℝ) ^ (151 : ℕ) ≤ (3 : ℝ) ^ (170 : ℕ) := by norm_num
  exact (mul_le_mul_of_nonneg_left he (by norm_num)).trans hnum

/-- The ordinary self-adjoint graph's 2K/4K² bounds fit the same C₃=3^170. -/
theorem compression_scale_le_paper (J : ℕ) (W : ℝ) (hJ : 1 ≤ J) :
    3 * reflectionSpectralScale J W ≤
      Real.exp (4 * J) * (((3 : ℝ) ^ (170 : ℕ)) * Real.sqrt W) ^ J := by
  let K := Real.exp (4 * J)
  let b := 2 * Real.exp 150 * Real.sqrt W
  let a := 6 * Real.exp 1
  have ha : 1 ≤ a := by dsimp [a]; linarith [Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)]
  have haJ : a ≤ a ^ J := by
    have ht := pow_le_pow_right₀ ha hJ
    simpa only [pow_one] using ht
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have ha' : 0 ≤ a := by linarith
  have hK : 0 ≤ K := (Real.exp_pos _).le
  have hid : a * b = 12 * Real.exp 151 * Real.sqrt W := by
    dsimp [a, b]
    rw [show (6 : ℝ) * Real.exp 1 * (2 * Real.exp 150 * Real.sqrt W) =
      12 * (Real.exp 1 * Real.exp 150) * Real.sqrt W by ring, ← Real.exp_add]
    norm_num
  have hroot : a * b ≤ ((3 : ℝ) ^ (170 : ℕ)) * Real.sqrt W := by
    rw [hid]
    exact mul_le_mul_of_nonneg_right compression_numeric_coefficient (Real.sqrt_nonneg _)
  calc
    _ = K * (a * b ^ J) := by dsimp [reflectionSpectralScale, reflectionTraceBase, K, a, b]; ring
    _ ≤ K * (a ^ J * b ^ J) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right haJ (pow_nonneg hb _)) hK
    _ = K * (a * b) ^ J := congrArg (fun z : ℝ => K * z) (mul_pow a b J).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg ha' hb) hroot J) hK

#print axioms compression_scale_le_paper

end ReflectedLiouville
