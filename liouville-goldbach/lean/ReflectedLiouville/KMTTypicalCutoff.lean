import ReflectedLiouville.KMTLogGains
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false
open Filter

namespace ReflectedLiouville

lemma halve_power_ge (T a b : ℝ) (hT : 0 < T) (hgain : 2 ≤ T ^ (a - b)) :
    T ^ b ≤ T ^ a / 2 := by
  have h := mul_le_mul_of_nonneg_right hgain (Real.rpow_nonneg hT.le b)
  have hid : T ^ (a - b) * T ^ b = T ^ a := by
    rw [← Real.rpow_add hT]
    congr 1
    ring
  rw [hid] at h
  linarith

lemma kmt_typical_log_cutoff (S T U ν θ : ℝ)
    (hS : 0 < S) (hT : 0 < T) (hST : S ≤ T) (hSν : T ^ ν ≤ S)
    (hU : min S (T ^ (2 / 5 : ℝ)) / 2 ≤ U)
    (hgain₁ : 2 ≤ T ^ (ν * (499 / 500 : ℝ) - θ))
    (hgain₂ : 2 ≤ T ^ ((199 / 500 : ℝ) - θ)) :
    T ^ θ ≤ (S ^ (-1 / 1000 : ℝ)) ^ (2 : ℕ) * U := by
  have hε : (S ^ (-1 / 1000 : ℝ)) ^ (2 : ℕ) = S ^ (-1 / 500 : ℝ) := by
    rw [← Real.rpow_mul_natCast hS.le]
    congr 1
    norm_num
  rw [hε]
  have hbase := mul_le_mul_of_nonneg_left hU (Real.rpow_nonneg hS.le (-1 / 500))
  by_cases hcase : S ≤ T ^ (2 / 5 : ℝ)
  · rw [min_eq_left hcase] at hbase
    have hid : S ^ (-1 / 500 : ℝ) * (S / 2) = S ^ (499 / 500 : ℝ) / 2 := by
      conv_lhs => rhs; rw [← Real.rpow_one S]
      rw [← mul_div_assoc, ← Real.rpow_add hS]
      norm_num
    rw [hid] at hbase
    calc
      _ ≤ T ^ (ν * (499 / 500 : ℝ)) / 2 := halve_power_ge T _ _ hT hgain₁
      _ ≤ S ^ (499 / 500 : ℝ) / 2 := by
        rw [Real.rpow_mul hT.le]
        exact div_le_div_of_nonneg_right (Real.rpow_le_rpow (by positivity) hSν (by norm_num)) (by norm_num)
      _ ≤ _ := hbase
  · have hcase' : T ^ (2 / 5 : ℝ) ≤ S := (lt_of_not_ge hcase).le
    rw [min_eq_right hcase'] at hbase
    have hpow := Real.rpow_le_rpow_of_nonpos hS hST (by norm_num : (-1 / 500 : ℝ) ≤ 0)
    have hproduct := mul_le_mul_of_nonneg_right hpow (by positivity : 0 ≤ T ^ (2 / 5 : ℝ) / 2)
    have hid : T ^ (-1 / 500 : ℝ) * (T ^ (2 / 5 : ℝ) / 2) = T ^ (199 / 500 : ℝ) / 2 := by
      rw [← mul_div_assoc, ← Real.rpow_add hT]
      norm_num
    rw [hid] at hproduct
    exact (halve_power_ge T _ _ hT hgain₂).trans (hproduct.trans hbase)

/-- Uniform growth of the actual typicality cutoff in both buffer regimes. -/
theorem eventually_kmt_typical_log_cutoff (ν : ℝ) (hν : 0 < ν) :
    ∀ᶠ X : ℝ in atTop, ∀ S U : ℝ, 0 < S → S ≤ Real.log X → (Real.log X) ^ ν ≤ S →
      min S ((Real.log X) ^ (2 / 5 : ℝ)) / 2 ≤ U →
      (Real.log X) ^ (min (ν / 2) (1 / 5 : ℝ)) ≤ (S ^ (-1 / 1000 : ℝ)) ^ (2 : ℕ) * U := by
  let θ := min (ν / 2) (1 / 5 : ℝ)
  have hθ₁ : θ ≤ ν / 2 := min_le_left _ _
  have hθ₂ : θ ≤ (1 / 5 : ℝ) := min_le_right _ _
  have hgap₁ : 0 < ν * (499 / 500 : ℝ) - θ := by linarith
  have hgap₂ : 0 < (199 / 500 : ℝ) - θ := by linarith
  have hg₁ := (tendsto_rpow_atTop hgap₁).comp Real.tendsto_log_atTop
  have hg₂ := (tendsto_rpow_atTop hgap₂).comp Real.tendsto_log_atTop
  filter_upwards [hg₁.eventually (eventually_ge_atTop (2 : ℝ)), hg₂.eventually (eventually_ge_atTop (2 : ℝ)),
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with X hg₁X hg₂X hT
  intro S U hS hST hSν hU
  exact kmt_typical_log_cutoff S (Real.log X) U ν θ hS hT hST hSν hU hg₁X hg₂X

#print axioms eventually_kmt_typical_log_cutoff

end ReflectedLiouville
