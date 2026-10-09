import ReflectedLiouville.HalaszTransfer
import ReflectedLiouville.CharacterAlgebra
import ReflectedLiouville.Corollary
import OAI.NumberTheory.TwoPointCorrelations.FinalMain

set_option autoImplicit false
open Filter
open scoped BigOperators
open OAI.TwoPointCorrelations

namespace ReflectedLiouville

lemma primesUpTo_floor_eq_sievePrimesUpTo (X : ℝ) :
    primesUpTo ⌊X⌋₊ = sievePrimesUpTo X := by
  ext p
  simp only [primesUpTo, sievePrimesUpTo, Finset.mem_filter, Finset.mem_range, Finset.mem_Iic]
  constructor <;> rintro ⟨hle, hp⟩ <;> exact ⟨by omega, hp⟩

/-- The untwisted distance for λ itself needs only the already proved Mertens input. -/
lemma eventually_liouville_untwisted_distance :
    ∀ᶠ X : ℝ in atTop,
      Real.log (Real.log X) / 2 ≤ squaredDistance liouville (modulusOneTwist 0) ⌊X⌋₊ := by
  obtain ⟨C, hC⟩ := primeReciprocalInput
  filter_upwards [eventually_ge_atTop (2 : ℝ),
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually
      (eventually_ge_atTop (2 * |C| + 1))] with X hX hlog
  rw [liouville_untwisted_distance, primesUpTo_floor_eq_sievePrimesUpTo]
  have hm := (abs_le.mp (hC X hX)).1
  change 2 * |C| + 1 ≤ Real.log (Real.log X) at hlog
  linarith [le_abs_self C, abs_nonneg C]

theorem liouville_mean_saving
    (h_MRT : MRTRealTwistRepulsionInput) :
    ∃ C X₀ : ℝ, 0 < C ∧ 100 ≤ X₀ ∧ ∀ X : ℝ, X₀ ≤ X →
      ‖∑ n ∈ Finset.Icc 1 ⌊X⌋₊, liouville n‖ ≤
        C * X / Real.rpow (Real.log X) (1 / 40) := by
  obtain ⟨C, X₁, hC, hX₁, hmean⟩ := real_mean_of_untwisted_distance h_MRT
  obtain ⟨X₂, hX₂⟩ := eventually_atTop.mp eventually_liouville_untwisted_distance
  refine ⟨C, max X₁ X₂, hC, hX₁.trans (le_max_left _ _), ?_⟩
  intro X hX
  exact hmean X ((le_max_left _ _).trans hX) liouville liouville_realMultiplicative liouville_one
    (fun m n _ _ => liouville_mul m n)
    (hX₂ X ((le_max_right _ _).trans hX))

#print axioms liouville_mean_saving

end ReflectedLiouville
