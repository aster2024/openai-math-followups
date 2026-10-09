import ReflectedLiouville.KMTMargins
import Mathlib.Tactic

set_option autoImplicit false
open Filter

namespace ReflectedLiouville

lemma kmt_epsilon_rpow (S a : ℝ) (hS : 0 ≤ S) :
    (S ^ (-1 / 1000 : ℝ)) ^ a = S ^ (-a / 1000) := by
  rw [← Real.rpow_mul hS]
  congr 1
  ring

lemma kmt_inner_accuracy (S T : ℝ) (hS : 1 < S) (hST : S ≤ T) :
    T ^ (-1 / 50 : ℝ) < (S ^ (-1 / 1000 : ℝ)) ^ (33 / 5 : ℝ) := by
  rw [kmt_epsilon_rpow S (33 / 5) (by linarith)]
  have hT : 1 < T := hS.trans_le hST
  calc
    _ < T ^ (-33 / 5000 : ℝ) := Real.rpow_lt_rpow_of_exponent_lt hT (by norm_num)
    _ ≤ _ := by
      have h := Real.rpow_le_rpow_of_nonpos (by linarith : 0 < S) hST (by norm_num : (-33 / 5000 : ℝ) ≤ 0)
      convert h using 1 <;> norm_num

lemma kmt_M_lower (S T : ℝ) (hS : 1 ≤ S) (hlogT : 1 ≤ Real.log T) :
    1 / Real.log T ≤ (S ^ (-1 / 1000 : ℝ)) ^ (-88 : ℝ) := by
  rw [kmt_epsilon_rpow S (-88) (by linarith)]
  calc
    _ ≤ 1 := (div_le_one (by linarith : 0 < Real.log T)).mpr hlogT
    _ ≤ _ := Real.one_le_rpow hS (by norm_num)

lemma kmt_M_upper_of_ratio (S T : ℝ) (hS : 0 < S) (hlogT : 0 < Real.log T)
    (hratio : 20 * S ^ (11 / 50 : ℝ) * Real.log T ≤ T) :
    (S ^ (-1 / 1000 : ℝ)) ^ (-88 : ℝ) ≤
      ((S ^ (-1 / 1000 : ℝ)) ^ (33 / 5 : ℝ)) ^ (20 : ℝ) * T / (20 * Real.log T) := by
  simp only [kmt_epsilon_rpow S _ hS.le]
  rw [← Real.rpow_mul hS.le]
  norm_num
  apply (le_div_iff₀ (by positivity : 0 < 20 * Real.log T)).mpr
  apply (mul_le_mul_iff_right₀ (Real.rpow_pos_of_pos hS (33 / 250 : ℝ))).mp
  have hadd : S ^ (33 / 250 : ℝ) * S ^ (11 / 125 : ℝ) = S ^ (11 / 50 : ℝ) := by
    rw [← Real.rpow_add hS]
    congr 1
    norm_num
  have hcancel : S ^ (33 / 250 : ℝ) * S ^ (-(33 / 250 : ℝ)) = 1 := by
    rw [← Real.rpow_add hS]
    norm_num
  calc
    _ = 20 * S ^ (11 / 50 : ℝ) * Real.log T := by
      rw [show S ^ (33 / 250 : ℝ) * (S ^ (11 / 125 : ℝ) * (20 * Real.log T)) =
        (S ^ (33 / 250 : ℝ) * S ^ (11 / 125 : ℝ)) * (20 * Real.log T) by ring, hadd]
      ring
    _ ≤ T := hratio
    _ = _ := by
      rw [← mul_assoc, hcancel, one_mul]

lemma eventually_kmt_M_ratio :
    ∀ᶠ X : ℝ in atTop, 20 * (Real.log X) ^ (11 / 50 : ℝ) * Real.log (Real.log X) ≤ Real.log X := by
  have hlim := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 39 / 50)).tendsto_div_nhds_zero
  have h := ((tendsto_const_nhds (x := (20 : ℝ))).mul hlim).comp Real.tendsto_log_atTop
  filter_upwards [h.eventually (eventually_le_nhds (by norm_num : 20 * (0 : ℝ) < 1)),
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with X hX hlog
  change 20 * (Real.log (Real.log X) / (Real.log X) ^ (39 / 50 : ℝ)) ≤ 1 at hX
  have hpow : 0 < (Real.log X) ^ (39 / 50 : ℝ) := Real.rpow_pos_of_pos hlog _
  have hX' : 20 * Real.log (Real.log X) ≤ (Real.log X) ^ (39 / 50 : ℝ) := by
    have hratio : 20 * Real.log (Real.log X) / (Real.log X) ^ (39 / 50 : ℝ) ≤ 1 := by
      simpa only [mul_div_assoc] using hX
    simpa only [one_mul] using (div_le_iff₀ hpow).mp hratio
  have hmul := mul_le_mul_of_nonneg_left hX' (Real.rpow_nonneg hlog.le (11 / 50))
  have heq : (Real.log X) ^ (11 / 50 : ℝ) * (Real.log X) ^ (39 / 50 : ℝ) = Real.log X := by
    rw [← Real.rpow_add hlog]
    norm_num
  rw [heq] at hmul
  convert hmul using 1 <;> ring

/-- The remaining reviewed inner-accuracy and M-admissibility margins,
    uniformly for all 1 < log R ≤ log X. -/
theorem eventually_kmt_inner_parameters :
    ∀ᶠ X : ℝ in atTop, ∀ S : ℝ, 1 < S → S ≤ Real.log X →
      (Real.log X) ^ (-1 / 50 : ℝ) < (S ^ (-1 / 1000 : ℝ)) ^ (33 / 5 : ℝ) ∧
      1 / Real.log (Real.log X) ≤ (S ^ (-1 / 1000 : ℝ)) ^ (-88 : ℝ) ∧
      (S ^ (-1 / 1000 : ℝ)) ^ (-88 : ℝ) ≤
        ((S ^ (-1 / 1000 : ℝ)) ^ (33 / 5 : ℝ)) ^ (20 : ℝ) * Real.log X /
          (20 * Real.log (Real.log X)) := by
  filter_upwards [eventually_kmt_M_ratio,
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually
      (eventually_ge_atTop (1 : ℝ))] with X hratio hloglog
  change 1 ≤ Real.log (Real.log X) at hloglog
  intro S hS hSX
  refine ⟨kmt_inner_accuracy S (Real.log X) hS hSX,
    kmt_M_lower S (Real.log X) hS.le hloglog, ?_⟩
  apply kmt_M_upper_of_ratio S (Real.log X) (by linarith) (by linarith)
  apply le_trans _ hratio
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by linarith) hSX (by norm_num)) (by norm_num))
    (by linarith)

#print axioms eventually_kmt_inner_parameters

end ReflectedLiouville
