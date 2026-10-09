import ReflectedLiouville.ZeroBox
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false
open Filter

namespace ReflectedLiouville

lemma log_power_width_identity (t b : ℝ) (ht : 0 < t) :
    Real.rpow t b * Real.log t / t = Real.log t / Real.rpow t (1 - b) := by
  simp only [Real.rpow_eq_pow]
  rw [Real.rpow_sub ht, Real.rpow_one]
  have hpow : Real.rpow t b ≠ 0 := (Real.rpow_pos_of_pos ht b).ne'
  field_simp

lemma eventually_log_power_width (b : ℝ) (hb : b < 1) :
    ∀ᶠ X : ℝ in atTop,
      Real.rpow (Real.log X) b * Real.log (Real.log X) / Real.log X < 1 / 8 := by
  have hlim := (isLittleO_log_rpow_atTop (sub_pos.mpr hb)).tendsto_div_nhds_zero
  have hlim' := hlim.comp Real.tendsto_log_atTop
  filter_upwards [hlim'.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 8)),
      Real.tendsto_log_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with X hX hlog
  rw [log_power_width_identity (Real.log X) b hlog]
  exact hX

lemma kmt_epsilon_power (S : ℝ) (hS : 0 ≤ S) :
    Real.rpow (Real.rpow S (-1 / 1000)) (-88) = Real.rpow S (11 / 125) := by
  simp only [Real.rpow_eq_pow]
  rw [← Real.rpow_mul hS]
  norm_num

/-- One threshold works for every smaller log R. This is the quantitative
    zero-box margin used in the variance proof, independent of q. -/
theorem eventually_kmt_zero_box_width :
    ∀ᶠ X : ℝ in atTop, ∀ R : ℝ, 1 < R → R ≤ X →
      Real.rpow (Real.rpow (Real.log R) (-1 / 1000)) (-88) *
        Real.log (Real.log X) / Real.log X < 1 / 8 := by
  filter_upwards [eventually_log_power_width (11 / 125) (by norm_num),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))] with X hX hlog
  intro R hR hRX
  have hRp : 0 < R := by linarith
  have hlogR : 0 < Real.log R := Real.log_pos hR
  rw [kmt_epsilon_power (Real.log R) hlogR.le]
  have hlogRX : Real.log R ≤ Real.log X := Real.log_le_log hRp hRX
  have hpow : Real.rpow (Real.log R) (11 / 125) ≤ Real.rpow (Real.log X) (11 / 125) :=
    Real.rpow_le_rpow hlogR.le hlogRX (by norm_num)
  apply lt_of_le_of_lt _ hX
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hpow (Real.log_nonneg hlog)) (by linarith)

#print axioms eventually_kmt_zero_box_width

end ReflectedLiouville
