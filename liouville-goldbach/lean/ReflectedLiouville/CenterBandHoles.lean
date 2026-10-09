import ReflectedLiouville.PrimeHoles
import ReflectedLiouville.FourierPowerMargins
import OAI.NumberTheory.TwoPoint.Bounds.ActualPrimeScale

set_option autoImplicit false
open Filter
open scoped BigOperators Topology
open OAI.TwoPointCorrelations

namespace ReflectedLiouville

lemma centeredPrimeSupply_deleted (E : Finset ℕ) (A W : ℝ) (i : ℕ) :
    centeredPrimeSupply E A W i = (centeredPrimeSupply ∅ A W i).filter (fun p => p ∉ E) := by
  classical
  ext p
  simp [centeredPrimeSupply, modFivePrimeBand, and_assoc]

lemma centered_supply_deletion_identity (E : Finset ℕ) (A W : ℝ) (i : ℕ) :
    (∑ p ∈ centeredPrimeSupply E A W i, (1 : ℝ) / p) +
      (∑ p ∈ (centeredPrimeSupply ∅ A W i).filter (fun p => p ∈ E), (1 : ℝ) / p) =
        ∑ p ∈ centeredPrimeSupply ∅ A W i, (1 : ℝ) / p := by
  classical
  rw [centeredPrimeSupply_deleted, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases h : p ∈ E <;> simp [h]

/-- The fixed empty-exclusion band estimate and the explicit hole cost are
    combined before varying N. No threshold depends on N.primeFactors. -/
theorem centered_band_mass_after_prime_holes (W : ℝ) (hW : 0 < W) :
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ (N : ℕ) [NeZero N] (A : ℝ), A₀ ≤ A →
      Real.log (N : ℝ) / (Real.exp A * A) ≤ W / 4 → ∀ i : ℕ,
        W ≤ primeHarmonicMass (centeredPrimeSupply N.primeFactors A W i) ∧
          primeHarmonicMass (centeredPrimeSupply N.primeFactors A W i) ≤ 2 * W := by
  obtain ⟨K, hK, hband⟩ := modFiveThetaInput.band_error ∅
  refine ⟨max 1 (16 * K / W), le_max_left _ _, ?_⟩
  intro N inst A hA hhole i
  have hA1 : 1 ≤ A := (le_max_left _ _).trans hA
  have hAp : 0 < A := by linarith
  let B := primeSupplyEndpoint A W i
  have hAB : A ≤ B := by
    have hm := primeSupplyEndpoint_mono A W hAp.le hW.le (Nat.zero_le i)
    rwa [primeSupplyEndpoint_zero] at hm
  have hBp : 0 < B := hAp.trans_le hAB
  have hB1 : 1 ≤ B := hA1.trans hAB
  have hBnext : B ≤ B * Real.exp (6 * W) := by
    have he := Real.one_le_exp (by positivity : 0 ≤ 6 * W)
    nlinarith
  have hmass := hband true B (B * Real.exp (6 * W)) hB1 hBnext
  have hlog : Real.log (B * Real.exp (6 * W)) - Real.log B = 6 * W := by
    rw [Real.log_mul hBp.ne' (Real.exp_pos _).ne', Real.log_exp]
    ring
  rw [hlog] at hmass
  norm_num only [modFiveDensity] at hmass
  have hstep : Real.exp (B * Real.exp (6 * W)) = Real.exp (primeSupplyEndpoint A W (i + 1)) := by
    rw [primeSupplyEndpoint_succ]
  rw [hstep] at hmass
  change |(∑ p ∈ centeredPrimeSupply ∅ A W i, (1 : ℝ) / p) - (1 / 4 : ℝ) * (6 * W)| ≤ 4 * K / B at hmass
  have hKsmall : 4 * K / B ≤ W / 4 := by
    have hKA : 16 * K / W ≤ A := (le_max_right _ _).trans hA
    have hkprod := (div_le_iff₀ hW).mp hKA
    apply (div_le_iff₀ hBp).mpr
    nlinarith
  let S := (centeredPrimeSupply ∅ A W i).filter (fun p => p ∈ N.primeFactors)
  have hS : S ⊆ N.primeFactors := by intro p hp; exact (Finset.mem_filter.mp hp).2
  have hH : 1 < Real.exp A := Real.one_lt_exp_iff.mpr hAp
  have hlo : ∀ p ∈ S, Real.exp A ≤ (p : ℝ) := by
    intro p hp
    have hp' := (Finset.mem_filter.mp hp).1
    have hm := centeredPrimeSupply_mem hp'
    have hlogp : A < Real.log (p : ℝ) := hAB.trans_lt hm.2.2.2.1
    have hpp : (0 : ℝ) < p := by exact_mod_cast hm.1.pos
    have he := Real.exp_lt_exp.mpr hlogp
    rw [Real.exp_log hpp] at he
    exact he.le
  have hcost := large_prime_factor_reciprocal_bound N S (Real.exp A) hS hH hlo
  rw [Real.log_exp] at hcost
  have hcost' : (∑ p ∈ S, (1 : ℝ) / p) ≤ W / 4 := hcost.trans hhole
  have heq := centered_supply_deletion_identity N.primeFactors A W i
  change (∑ p ∈ centeredPrimeSupply N.primeFactors A W i, (1 : ℝ) / p) +
      (∑ p ∈ S, (1 : ℝ) / p) = _ at heq
  rw [primeHarmonicMass_eq_sum]
  have hn : 0 ≤ ∑ p ∈ S, (1 : ℝ) / p := Finset.sum_nonneg (fun _ _ => by positivity)
  obtain ⟨hmlo, hmhi⟩ := abs_le.mp hmass
  constructor <;> linarith

lemma power_exp_power_tendsto_zero (a α : ℝ) (hα : 0 < α) :
    Tendsto (fun L : ℝ => L ^ a / Real.exp (L ^ α)) atTop (𝓝 0) := by
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (a / α) 1 (by norm_num)).comp
    (tendsto_rpow_atTop hα)
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  change (L ^ α) ^ (a / α) * Real.exp (-1 * L ^ α) = L ^ a / Real.exp (L ^ α)
  rw [← Real.rpow_mul hL.le, mul_div_cancel₀ _ hα.ne', neg_one_mul, Real.exp_neg, div_eq_mul_inv]

/-- Uniform center-band masses for the actual varying excluded prime factors. -/
theorem eventually_center_band_masses (a α W : ℝ) (hα : 0 < α) (hW : 0 < W) :
    ∀ᶠ L : ℝ in atTop, ∀ (N : ℕ) [NeZero N], Real.log (N : ℝ) ≤ L ^ a →
      ∀ i : ℕ, W ≤ primeHarmonicMass (centeredPrimeSupply N.primeFactors (L ^ α) W i) ∧
        primeHarmonicMass (centeredPrimeSupply N.primeFactors (L ^ α) W i) ≤ 2 * W := by
  obtain ⟨A₀, hA₀, hm⟩ := centered_band_mass_after_prime_holes W hW
  filter_upwards [(tendsto_rpow_atTop hα).eventually (eventually_ge_atTop A₀),
    (power_exp_power_tendsto_zero a α hα).eventually (eventually_le_nhds (by linarith : (0 : ℝ) < W / 4)),
    eventually_ge_atTop (1 : ℝ)] with L hA hsmall hL
  intro N inst hN i
  apply hm N (L ^ α) hA
  have hA1 : 1 ≤ L ^ α := Real.one_le_rpow hL hα.le
  have hexp : 0 < Real.exp (L ^ α) := Real.exp_pos _
  have hden : Real.exp (L ^ α) ≤ Real.exp (L ^ α) * L ^ α := by nlinarith
  calc
    _ ≤ L ^ a / (Real.exp (L ^ α) * L ^ α) := div_le_div_of_nonneg_right hN (by positivity)
    _ ≤ L ^ a / Real.exp (L ^ α) := div_le_div_of_nonneg_left (by positivity) hexp hden
    _ ≤ _ := hsmall

#print axioms eventually_center_band_masses

end ReflectedLiouville
