import ReflectedLiouville.LiouvilleMean
import ReflectedLiouville.Casts
import ReflectedLiouville.Corollary

set_option autoImplicit false
open Filter
open scoped BigOperators

namespace ReflectedLiouville

lemma linearSum_endpoint (N : ℕ) (hN : 1 ≤ N) :
    (linearSum N : ℂ) = (∑ n ∈ Finset.Icc 1 N, liouville n) - liouville N := by
  classical
  have hset : Finset.Icc 1 N = insert N (reflectedIndices N) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert, reflectedIndices, Finset.mem_Ico]
    omega
  have hnot : N ∉ reflectedIndices N := by simp [reflectedIndices]
  rw [hset, Finset.sum_insert hnot, ← linearSum_cast]
  ring

lemma linearSum_le_mean_and_one (N : ℕ) (hN : 1 ≤ N) :
    |linearSum N| ≤ ‖∑ n ∈ Finset.Icc 1 N, liouville n‖ + 1 := by
  calc
    _ = ‖(linearSum N : ℂ)‖ := by rw [Complex.norm_real, Real.norm_eq_abs]
    _ ≤ ‖∑ n ∈ Finset.Icc 1 N, liouville n‖ + ‖liouville N‖ := by
      rw [linearSum_endpoint N hN]
      exact norm_sub_le _ _
    _ ≤ _ := add_le_add le_rfl (norm_liouville_le N)

/-- The linear part uses proved library Halasz and the published MRT input. -/
theorem liouville_linear_log_saving
    (h_MRT : MRTRealTwistRepulsionInput) : LinearLogSaving := by
  obtain ⟨C, X₀, hC, hX₀, hmean⟩ := liouville_mean_saving h_MRT
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp (log_saving_error_eventually_ge_one (1 / 40))
  refine ⟨1 / 40, by norm_num, C + 1, by positivity,
    max 3 (max ⌈X₀⌉₊ N₁), le_max_left _ _, ?_⟩
  intro N hN
  have hN3 : 3 ≤ N := (le_max_left _ _).trans hN
  have hceil : ⌈X₀⌉₊ ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNX₀ : X₀ ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hceil)
  have hbound : ‖∑ n ∈ Finset.Icc 1 N, liouville n‖ ≤
      C * (N : ℝ) / Real.rpow (Real.log (N : ℝ)) (1 / 40) := by
    simpa only [Nat.floor_natCast] using hmean (N : ℝ) hNX₀
  have herror := hN₁ N ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  apply (linearSum_le_mean_and_one N (by omega)).trans
  calc
    _ ≤ C * (N : ℝ) / Real.rpow (Real.log (N : ℝ)) (1 / 40) +
        (N : ℝ) / Real.rpow (Real.log (N : ℝ)) (1 / 40) := by linarith
    _ = _ := by ring

/-- This completes the corollary reduction; the reflected saving is still a
    derived project target, not an added published hypothesis. -/
theorem sign_patterns_of_reflected_saving
    (h_MRT : MRTRealTwistRepulsionInput)
    (h_reflected : ReflectedLogSaving) : SignPatternLogSaving :=
  sign_patterns_of_two_savings h_reflected (liouville_linear_log_saving h_MRT)

#print axioms liouville_linear_log_saving
#print axioms sign_patterns_of_reflected_saving

end ReflectedLiouville
