import ReflectedLiouville.PrimeDistance
import ReflectedLiouville.HalaszTransfer
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false
open Filter
open scoped BigOperators
open OAI.TwoPointCorrelations

namespace ReflectedLiouville

lemma eventually_loglog_polylog_margin (A B : ℝ) :
    ∀ᶠ X : ℝ in atTop,
      Real.log (Real.log X) / 2 ≤ Real.log (Real.log X) -
        Real.log (Real.log ((Real.log X) ^ (64 : ℕ))) - 2 * A - B := by
  have hll := Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have hratio := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero
  have hratio' := hratio.comp hll
  filter_upwards [hratio'.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 4)),
    hll.eventually (eventually_ge_atTop (4 * (Real.log 64 + 2 * A + B))),
    hll.eventually (eventually_ge_atTop (1 : ℝ))] with X hr hbig hpos
  change 1 ≤ Real.log (Real.log X) at hpos
  have hTpos : 0 < Real.log (Real.log X) := by linarith
  change 4 * (Real.log 64 + 2 * A + B) ≤ Real.log (Real.log X) at hbig
  change Real.log (Real.log (Real.log X)) / (Real.log (Real.log X)) ^ (1 : ℝ) ≤ 1 / 4 at hr
  rw [Real.rpow_one] at hr
  have hr' := (div_le_iff₀ hTpos).mp hr
  rw [Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  rw [Real.log_mul (by norm_num : (64 : ℝ) ≠ 0) hTpos.ne']
  linarith

lemma polylog_cutoff_ge_two (X : ℝ) (hlog : 2 ≤ Real.log X) :
    2 ≤ (Real.log X) ^ (64 : ℕ) := by
  have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hlog 64
  have htwo : (2 : ℝ) ≤ 2 ^ (64 : ℕ) := by norm_num
  exact htwo.trans hpow

/-- The prime tail target, if derived, implies the full uniform real-character
    distance estimate. It is never asserted as a published premise. -/
theorem real_character_distance_of_prime_tail (h_tail : RealCharacterPrimeTailBound) :
    ∃ X₀ : ℝ, 100 ≤ X₀ ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ X →
        ∀ χ : DirichletCharacter ℂ q, RealCharacter χ →
          Real.log (Real.log X) / 2 ≤
            squaredDistance (fun n => liouville n * χ (n : ZMod q)) (modulusOneTwist 0) ⌊X⌋₊ := by
  obtain ⟨B, X₁, hB, hX₁, htail⟩ := h_tail
  obtain ⟨A, hA⟩ := primeReciprocalInput
  obtain ⟨X₂, hX₂⟩ := eventually_atTop.mp (eventually_loglog_polylog_margin A B)
  obtain ⟨X₃, hX₃⟩ := eventually_atTop.mp
    (Real.tendsto_log_atTop.eventually (eventually_ge_atTop (2 : ℝ)))
  refine ⟨max (max X₁ X₂) X₃, hX₁.trans ((le_max_left _ _).trans (le_max_left _ _)), ?_⟩
  intro X hX q inst hqX χ hχ
  have hXX₁ : X₁ ≤ X := (le_max_left _ _).trans ((le_max_left _ _).trans hX)
  have hXX₂ : X₂ ≤ X := (le_max_right _ _).trans ((le_max_left _ _).trans hX)
  have hXX₃ : X₃ ≤ X := (le_max_right _ _).trans hX
  have hX100 : 100 ≤ X := hX₁.trans hXX₁
  have hlog := hX₃ X hXX₃
  have hfull := (abs_le.mp (hA X (by linarith : 2 ≤ X))).1
  have hlow := (abs_le.mp (hA ((Real.log X) ^ (64 : ℕ)) (polylog_cutoff_ge_two X hlog))).2
  have hmargin := hX₂ X hXX₂
  by_cases hprincipal : χ = 1
  · rw [liouville_character_untwisted_distance, primesUpTo_floor_eq_sievePrimesUpTo]
    have hnonneg : 0 ≤ ∑ p ∈ sievePrimesUpTo X, (χ (p : ZMod q)).re / p := by
      apply Finset.sum_nonneg
      intro p hp
      rw [hprincipal]
      exact div_nonneg (principal_prime_re_nonneg p) (Nat.cast_nonneg p)
    have hsmall := small_prime_reciprocal_sum_le X ((Real.log X) ^ (64 : ℕ)) (by positivity)
    have hgoodlow : 0 ≤ Real.log (Real.log ((Real.log X) ^ (64 : ℕ))) + A := by
      have hsum : 0 ≤ ∑ p ∈ sievePrimesUpTo ((Real.log X) ^ (64 : ℕ)), (1 : ℝ) / p := by
        apply Finset.sum_nonneg
        intro p hp
        positivity
      linarith
    linarith
  · have hb := (abs_le.mp (htail X hXX₁ q hqX χ hχ hprincipal)).1
    have hderived := character_distance_lower_from_tail χ X ((Real.log X) ^ (64 : ℕ)) A B
      (by positivity) (by linarith) (by linarith) hb
    exact hmargin.trans hderived

theorem real_character_mean_of_prime_tail
    (h_MRT : MRTRealTwistRepulsionInput)
    (h_tail : RealCharacterPrimeTailBound) : RealCharacterMeanBound := by
  obtain ⟨C, X₁, hC, hX₁, hmean⟩ := real_mean_of_untwisted_distance h_MRT
  obtain ⟨X₂, hX₂, hdist⟩ := real_character_distance_of_prime_tail h_tail
  refine ⟨C, max X₁ X₂, hC, (by linarith : 10 ≤ X₁).trans (le_max_left _ _), ?_⟩
  intro X hX q inst hqX χ hχ
  exact hmean X ((le_max_left _ _).trans hX) _ (liouville_character_realMultiplicative χ hχ)
    (by simpa only [Nat.cast_one] using liouville_character_one χ) (liouville_character_complete χ)
    (hdist X ((le_max_right _ _).trans hX) q hqX χ hχ)

#print axioms real_character_mean_of_prime_tail

end ReflectedLiouville
