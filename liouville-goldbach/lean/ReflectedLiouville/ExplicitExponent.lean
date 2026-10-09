import ReflectedLiouville.ExplicitBinnedSaving
import ReflectedLiouville.LinearSaving

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Filter
open scoped Classical
namespace ReflectedLiouville

theorem log_saving_of_binned_estimate_at_exponent (A : ℕ) (hA : 0 < A) (W δ : ℝ)
    (hW : 0 < W) (hδ : 0 < δ) (hbin : BinnedReflectedSaving A W δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      |reflectedSum N| ≤ C*(N : ℝ)/Real.rpow (Real.log (N : ℝ)) (δ/(6*W*(A : ℝ))) := by
  obtain ⟨C, hC, N₀, hN₀, hb⟩ := hbin
  let c := δ / (6 * W * (A : ℝ))
  have hAr : (0 : ℝ) < A := by exact_mod_cast hA
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨C * Real.exp 1, by positivity, N₀, hN₀, ?_⟩
  intro N hN
  have hn : 3 ≤ N := hN₀.trans hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  let L := (Real.log (N : ℝ)) ^ (1 / (A : ℝ))
  let J := reflectionBandCount W δ L
  have hL : 0 < L := Real.rpow_pos_of_pos hlog _
  have hfloor := Nat.lt_floor_add_one (δ * Real.log L / (6 * W))
  have hexp : Real.exp (-(J : ℝ)) ≤ Real.exp (1 - δ * Real.log L / (6 * W)) := by
    apply Real.exp_le_exp.mpr
    change δ * Real.log L / (6 * W) < (J : ℝ) + 1 at hfloor
    linarith only [hfloor]
  have hlogId : δ * Real.log L / (6 * W) = c * Real.log (Real.log (N : ℝ)) := by
    dsimp only [L, c]
    rw [Real.log_rpow hlog]
    field_simp [hW.ne', hAr.ne']
    <;> ring
  have hpower : Real.exp (1 - c * Real.log (Real.log (N : ℝ))) =
      Real.exp 1 * (Real.log (N : ℝ)) ^ (-c) := by
    rw [Real.exp_sub, Real.rpow_def_of_pos hlog]
    rw [show Real.log (Real.log (N : ℝ)) * (-c) = -(c * Real.log (Real.log (N : ℝ))) by ring,
      Real.exp_neg]
    ring
  rw [hlogId, hpower] at hexp
  have hbound := (hb N hN).trans (mul_le_mul_of_nonneg_left hexp hC.le)
  have hsum := (div_le_iff₀ hNr).mp hbound
  change |reflectedSum N| ≤ (C*Real.exp 1)*(N : ℝ)/Real.rpow (Real.log (N : ℝ)) c
  apply hsum.trans_eq
  simp only [Real.rpow_eq_pow, Real.rpow_neg hlog.le, div_eq_mul_inv]
  ring

lemma paper_star_exponent_value :
    (1/100000 : ℝ)/(6*((10 : ℝ)^(180 : ℕ))*(1000000 : ℕ)) =
      1/(6*((10 : ℝ)^(191 : ℕ))) := by norm_num

lemma paper_exponent_le_star :
    (1 : ℝ)/(10 : ℝ)^(200 : ℕ) ≤
      (1/100000 : ℝ)/(6*((10 : ℝ)^(180 : ℕ))*(1000000 : ℕ)) := by norm_num

lemma paper_exponent_le_linear :
    (1 : ℝ)/(10 : ℝ)^(200 : ℕ) ≤ (1/40 : ℝ) := by norm_num

theorem explicit_liouville_correlation
    (h_KMT : KMTInput) (h_MRT : MRTRealTwistRepulsionInput) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      |reflectedSum N| ≤ C*(N : ℝ)/Real.rpow (Real.log (N : ℝ)) (1/(10 : ℝ)^(200 : ℕ)) := by
  obtain ⟨C,hC,N₁,hN₁,hb⟩ := log_saving_of_binned_estimate_at_exponent 1000000 (by norm_num)
    ((10 : ℝ)^(180 : ℕ)) (1/100000) (by positivity) (by norm_num)
    (explicit_binned_reflected_saving h_KMT h_MRT)
  obtain ⟨N₂,hN₂⟩ := eventually_atTop.mp
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (1 : ℝ)))
  refine ⟨C,hC,max N₁ N₂,hN₁.trans (le_max_left _ _),?_⟩
  intro N hN
  have hn := hb N ((le_max_left _ _).trans hN)
  have hlog := hN₂ N ((le_max_right _ _).trans hN)
  exact hn.trans (log_saving_error_antitone N hlog _ _ C hC.le paper_exponent_le_star)

#print axioms explicit_liouville_correlation
end ReflectedLiouville
