import ReflectedLiouville.FinalReduction
import ReflectedLiouville.RoughConvolutionScales
import ReflectedLiouville.ReducedPaddingCost

set_option autoImplicit false
open Filter

namespace ReflectedLiouville

lemma spectral_numeric_gain :
    Real.exp 6 * (3 : ℝ) ^ (170 : ℕ) ≤ Real.sqrt ((10 : ℝ) ^ (180 : ℕ)) := by
  have hExp : Real.exp 6 ≤ (3 : ℝ) ^ (6 : ℕ) := by
    have hid : Real.exp 6 = (Real.exp 1) ^ (6 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
    rw [hid]
    exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le 6
  have hnum : (3 : ℝ) ^ (6 : ℕ) * (3 : ℝ) ^ (170 : ℕ) ≤ (10 : ℝ) ^ (90 : ℕ) := by norm_num
  have hsqrt : Real.sqrt ((10 : ℝ) ^ (180 : ℕ)) = (10 : ℝ) ^ (90 : ℕ) := by
    have hp : (10 : ℝ) ^ (180 : ℕ) = ((10 : ℝ) ^ (90 : ℕ)) ^ (2 : ℕ) := by rw [← pow_mul]
    rw [hp, Real.sqrt_sq (by positivity)]
  rw [hsqrt]
  exact (mul_le_mul_of_nonneg_right hExp (by positivity)).trans hnum

lemma spectral_error_decay (J : ℕ) :
    Real.exp (5 * J) * (((3 : ℝ) ^ (170 : ℕ)) / Real.sqrt ((10 : ℝ) ^ (180 : ℕ))) ^ J ≤
      Real.exp (-(J : ℝ)) := by
  have hs : 0 < Real.sqrt ((10 : ℝ) ^ (180 : ℕ)) := Real.sqrt_pos.mpr (by positivity)
  have hratio : ((3 : ℝ) ^ (170 : ℕ)) / Real.sqrt ((10 : ℝ) ^ (180 : ℕ)) ≤ Real.exp (-6) := by
    rw [Real.exp_neg, inv_eq_one_div]
    apply (div_le_div_iff₀ hs (Real.exp_pos 6)).mpr
    simpa only [one_mul, mul_comm] using spectral_numeric_gain
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ ((3 : ℝ) ^ (170 : ℕ)) /
    Real.sqrt ((10 : ℝ) ^ (180 : ℕ))) hratio J
  have ht := mul_le_mul_of_nonneg_left hp (Real.exp_pos (5 * J)).le
  apply ht.trans_eq
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  ring

lemma centering_error_decay (W L : ℝ) (hW : 1 ≤ W) (hL : 1 ≤ L) :
    let J := reflectionBandCount W (1 / 100000) L
    Real.exp (J : ℝ) * (2 : ℝ) ^ J * L ^ (-1 / 100000 : ℝ) ≤ Real.exp (-(J : ℝ)) := by
  dsimp only
  let J := reflectionBandCount W (1 / 100000) L
  have hJ : (0 : ℝ) ≤ J := Nat.cast_nonneg _
  have hLp : 0 < L := by linarith
  have hlog : 0 ≤ Real.log L := Real.log_nonneg hL
  have hb := reflectionBandCount_mul_bound W (1 / 100000) L (by linarith) (by norm_num) hL
  have hWJ := mul_nonneg (sub_nonneg.mpr hW) hJ
  have hlog2 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hJlog2 := mul_le_mul_of_nonneg_left hlog2 hJ
  have hpower2 : (2 : ℝ) ^ J = Real.exp ((J : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  rw [hpower2, Real.rpow_def_of_pos hLp, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  change (J : ℝ) * (6 * W) ≤ (1 / 100000 : ℝ) * Real.log L at hb
  nlinarith only [hb, hWJ, hJlog2, hlog]

#print axioms spectral_error_decay
#print axioms centering_error_decay

end ReflectedLiouville
