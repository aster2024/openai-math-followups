import ReflectedLiouville.KMTAccuracy
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false
open Filter

namespace ReflectedLiouville

theorem eventually_kmt_log_gains (ν : ℝ) (hν : 0 < ν) :
    ∀ᶠ X : ℝ in atTop, ∀ S : ℝ, (Real.log X) ^ ν ≤ S →
      1 < S ∧ 30 ≤ min S ((Real.log X) ^ (2 / 5 : ℝ)) ∧
        2 ≤ S ^ (39 / 10000 : ℝ) ∧ 2 ≤ (Real.log X) ^ (9 / 10000 : ℝ) := by
  let μ := min ν (2 / 5 : ℝ)
  have hμ : 0 < μ := lt_min hν (by norm_num)
  have hmin := (tendsto_rpow_atTop hμ).comp Real.tendsto_log_atTop
  have hgainS := (tendsto_rpow_atTop (mul_pos hν (by norm_num : (0 : ℝ) < 39 / 10000))).comp Real.tendsto_log_atTop
  have hgainT := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 9 / 10000)).comp Real.tendsto_log_atTop
  filter_upwards [hmin.eventually (eventually_ge_atTop (30 : ℝ)),
    hgainS.eventually (eventually_ge_atTop (2 : ℝ)),
    hgainT.eventually (eventually_ge_atTop (2 : ℝ)),
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (1 : ℝ))] with X hM hGS hGT hT
  intro S hS
  have hTpos : 0 < Real.log X := by linarith
  have hμν : (Real.log X) ^ μ ≤ (Real.log X) ^ ν :=
    Real.rpow_le_rpow_of_exponent_le hT.le (min_le_left _ _)
  have hμcap : (Real.log X) ^ μ ≤ (Real.log X) ^ (2 / 5 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hT.le (min_le_right _ _)
  have hmin30 : 30 ≤ min S ((Real.log X) ^ (2 / 5 : ℝ)) :=
    le_min (hM.trans (hμν.trans hS)) (hM.trans hμcap)
  have hSpos : 0 < S := by linarith [(min_le_left S ((Real.log X) ^ (2 / 5 : ℝ))).trans' hmin30]
  have hS1 : 1 < S := by have h := hmin30.trans (min_le_left _ _); linarith
  change 2 ≤ (Real.log X) ^ (ν * (39 / 10000 : ℝ)) at hGS
  rw [Real.rpow_mul hTpos.le] at hGS
  have hGS' := hGS.trans (Real.rpow_le_rpow (by positivity) hS (by norm_num))
  change 2 ≤ (Real.log X) ^ (9 / 10000 : ℝ) at hGT
  exact ⟨hS1, hmin30, hGS', hGT⟩

#print axioms eventually_kmt_log_gains

end ReflectedLiouville
