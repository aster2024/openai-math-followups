import ReflectedLiouville.KMTEpsilon
import Mathlib.Tactic

set_option autoImplicit false

namespace ReflectedLiouville

lemma half_negative_power_bound (S a : ℝ) (hS : 0 < S) (ha : a ≤ 1) :
    (S / 2) ^ (-a) ≤ 2 * S ^ (-a) := by
  have heq : (S / 2) ^ (-a) = S ^ (-a) * (2 : ℝ) ^ a := by
    rw [Real.div_rpow hS.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    field_simp
  rw [heq]
  have hp : (2 : ℝ) ^ a ≤ 2 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) ha
  nlinarith [Real.rpow_nonneg hS.le (-a)]

lemma power_gain_absorbs_two (S a b : ℝ) (hS : 0 < S) (hgain : 2 ≤ S ^ (a - b)) :
    2 * S ^ (-a) ≤ S ^ (-b) := by
  have h := mul_le_mul_of_nonneg_right hgain (Real.rpow_nonneg hS.le (-a))
  have hid : S ^ (a - b) * S ^ (-a) = S ^ (-b) := by
    rw [← Real.rpow_add hS]
    congr 1
    ring
  rwa [hid] at h

/-- Pointwise lower-accuracy test from the two log-buffer regimes.
    S=log R, T=log X, U=log R_* in the manuscript. -/
lemma kmt_accuracy_of_log_lower (S T U : ℝ)
    (hS : 0 < S) (hT : 0 < T) (hST : S ≤ T)
    (hU : min S (T ^ (2 / 5 : ℝ)) / 2 ≤ U)
    (hgainS : 2 ≤ S ^ (39 / 10000 : ℝ))
    (hgainT : 2 ≤ T ^ (9 / 10000 : ℝ)) :
    U ^ (-1 / 200 : ℝ) ≤ (S ^ (-1 / 1000 : ℝ)) ^ (11 / 10 : ℝ) := by
  rw [kmt_epsilon_rpow S (11 / 10) hS.le]
  have hUp : 0 < U := (by positivity : 0 < min S (T ^ (2 / 5 : ℝ)) / 2).trans_le hU
  by_cases hcase : S ≤ T ^ (2 / 5 : ℝ)
  · rw [min_eq_left hcase] at hU
    calc
      _ ≤ (S / 2) ^ (-1 / 200 : ℝ) := Real.rpow_le_rpow_of_nonpos (by positivity) hU (by norm_num)
      _ ≤ 2 * S ^ (-1 / 200 : ℝ) := by
        simpa only [neg_div] using half_negative_power_bound S (1 / 200) hS (by norm_num)
      _ ≤ S ^ (-11 / 10000 : ℝ) := by
        have hgain : 2 ≤ S ^ ((1 / 200 : ℝ) - 11 / 10000) := by
          convert hgainS using 1 <;> norm_num
        simpa only [neg_div] using power_gain_absorbs_two S (1 / 200) (11 / 10000) hS hgain
      _ = _ := by congr 1; norm_num
  · have hcase' : T ^ (2 / 5 : ℝ) ≤ S := (lt_of_not_ge hcase).le
    rw [min_eq_right hcase'] at hU
    calc
      _ ≤ (T ^ (2 / 5 : ℝ) / 2) ^ (-1 / 200 : ℝ) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hU (by norm_num)
      _ ≤ 2 * (T ^ (2 / 5 : ℝ)) ^ (-1 / 200 : ℝ) := by
        simpa only [neg_div] using half_negative_power_bound (T ^ (2 / 5 : ℝ)) (1 / 200)
          (Real.rpow_pos_of_pos hT _) (by norm_num)
      _ = 2 * T ^ (-1 / 500 : ℝ) := by
        rw [← Real.rpow_mul hT.le]
        congr 1
        norm_num
      _ ≤ T ^ (-11 / 10000 : ℝ) := by
        have hgain : 2 ≤ T ^ ((1 / 500 : ℝ) - 11 / 10000) := by
          convert hgainT using 1 <;> norm_num
        simpa only [neg_div] using power_gain_absorbs_two T (1 / 500) (11 / 10000) hT hgain
      _ ≤ S ^ (-11 / 10000 : ℝ) := Real.rpow_le_rpow_of_nonpos hS hST (by norm_num)
      _ = _ := by congr 1; norm_num

#print axioms kmt_accuracy_of_log_lower

end ReflectedLiouville
