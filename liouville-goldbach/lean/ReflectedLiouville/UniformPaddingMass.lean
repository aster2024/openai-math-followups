import OAI.NumberTheory.TwoPointCorrelations.FinalMain
import OAI.NumberTheory.TwoPoint.Bounds.PaddingBinMassTotal

set_option autoImplicit false
open Filter
open scoped BigOperators
open OAI.TwoPointCorrelations

namespace ReflectedLiouville

lemma reciprocal_padding_count_mono {Q R : Finset ℕ} (hQR : Q ⊆ R) :
    (reciprocalPaddingLaw Q).average booleanCount ≤
      (reciprocalPaddingLaw R).average booleanCount := by
  rw [reciprocal_padding_count_average, reciprocal_padding_count_average,
    Finset.sum_coe_sort Q (fun p => (4 : ℝ) / ((p : ℝ) + 4)),
    Finset.sum_coe_sort R (fun p => (4 : ℝ) / ((p : ℝ) + 4))]
  exact Finset.sum_le_sum_of_subset_of_nonneg hQR (fun _ _ _ => by positivity)

lemma reciprocal_padding_log_mono {Q R : Finset ℕ} (hQR : Q ⊆ R) :
    (reciprocalPaddingLaw Q).average (paddingLog Q) ≤
      (reciprocalPaddingLaw R).average (paddingLog R) := by
  rw [reciprocal_padding_log_average, reciprocal_padding_log_average,
    Finset.sum_coe_sort Q (fun p => ((4 : ℝ) / ((p : ℝ) + 4)) * Real.log p),
    Finset.sum_coe_sort R (fun p => ((4 : ℝ) / ((p : ℝ) + 4)) * Real.log p)]
  exact Finset.sum_le_sum_of_subset_of_nonneg hQR
    (fun p _ _ => mul_nonneg (by positivity) (log_nat_nonneg p))

lemma padding_probability_from_moments (Q : Finset ℕ) (L : ℝ) (hL : 1 < L)
    (hc : (reciprocalPaddingLaw Q).average booleanCount ≤ 4 * Real.log L)
    (hl : (reciprocalPaddingLaw Q).average (paddingLog Q) ≤ 4 * L) :
    (1 / 2 : ℝ) ≤ (reciprocalPaddingLaw Q).probability
      (fun b => booleanCount b ≤ 100 * Real.log L ∧ paddingLog Q b ≤ 98 * L) := by
  let μ := reciprocalPaddingLaw Q
  have hLp : 0 < L := by linarith
  have hlog : 0 < Real.log L := Real.log_pos hL
  have hcount : μ.probability (fun b => 100 * Real.log L < booleanCount b) ≤ 1 / 25 := by
    apply (μ.probability_lt_le_average booleanCount booleanCount_nonneg
      (100 * Real.log L) (by positivity)).trans
    calc
      _ ≤ (4 * Real.log L) / (100 * Real.log L) := div_le_div_of_nonneg_right hc (by positivity)
      _ = _ := by field_simp; norm_num
  have hsize : μ.probability (fun b => 98 * L < paddingLog Q b) ≤ 2 / 49 := by
    apply (μ.probability_lt_le_average (paddingLog Q) (paddingLog_nonneg Q)
      (98 * L) (by positivity)).trans
    calc
      _ ≤ (4 * L) / (98 * L) := div_le_div_of_nonneg_right hl (by positivity)
      _ = _ := by field_simp; norm_num
  have hboth := μ.probability_and_ge (fun b => booleanCount b ≤ 100 * Real.log L)
    (fun b => paddingLog Q b ≤ 98 * L)
  simp only [not_le] at hboth
  linarith

/-- The exclusions follow the threshold: this is valid for the changing prime
    factors of N, unlike a theorem with E fixed before L. -/
theorem eventually_uniform_padding_retention :
    ∀ᶠ L : ℝ in atTop, ∀ Q : Finset ℕ, Q ⊆ paddingPrimeSupply ∅ L →
      (1 / 2 : ℝ) ≤ (reciprocalPaddingLaw Q).probability
        (fun b => booleanCount b ≤ 100 * Real.log L ∧ paddingLog Q b ≤ 98 * L) := by
  filter_upwards [modFiveThetaInput.eventually_reciprocal_padding_count_mean ∅,
    modFiveThetaInput.eventually_reciprocal_padding_log_mean ∅,
    eventually_gt_atTop (1 : ℝ)] with L hc hl hL
  intro Q hQ
  apply padding_probability_from_moments Q L hL
  · exact (reciprocal_padding_count_mono hQ).trans hc
  · have hl' : (reciprocalPaddingLaw (paddingPrimeSupply ∅ L)).average
        (paddingLog (paddingPrimeSupply ∅ L)) ≤ 4 * L := by
      rwa [reciprocal_padding_log_average]
    exact (reciprocal_padding_log_mono hQ).trans hl'

/-- Retained bin mass for every reduced padding pool and every admissible tuple
    family, with all varying objects quantified after the L threshold. -/
theorem uniform_retained_padding_mass :
    ∀ᶠ L : ℝ in atTop, ∀ (D Q : Finset ℕ) (η : ℝ),
      Q ⊆ paddingPrimeSupply ∅ L → 0 < η →
      (∀ d ∈ D, 0 < d ∧ Real.log d ≤ 2 * L) →
      (1 / 2 : ℝ) * paddingTiltNormalizer Q * (∑ d ∈ D, 1 / (d : ℝ)) ≤
        totalPaddingBinMass D Q L η := by
  filter_upwards [eventually_uniform_padding_retention] with L hL
  intro D Q η hQ hη hD
  exact (totalPaddingBinMass_bounds D Q
    (fun p hp => paddingPrimeSupply_prime (hQ hp)) hη (hL Q hQ) hD).1

#print axioms uniform_retained_padding_mass

end ReflectedLiouville
