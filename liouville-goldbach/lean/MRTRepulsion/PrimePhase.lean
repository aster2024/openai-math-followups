import MRTRepulsion.Algebra
import MRTRepulsion.PhaseIntegral
import OAI.NumberTheory.TwoPoint.Fourier.ModFivePrimeNumberTheorem
import Mathlib.Analysis.Complex.ExponentialBounds

set_option autoImplicit false
open scoped BigOperators Classical
open OAI.TwoPointCorrelations
open Finset MeasureTheory

namespace MRTRepulsion

noncomputable def bandPhase (t a b : ℝ) : ℝ :=
  ∑ p ∈ mrtPrimeBand a b, (1 - Real.cos (t*Real.log (p : ℝ))) / p

lemma bandPhase_nonneg (t a b : ℝ) : 0 ≤ bandPhase t a b := by
  apply sum_nonneg
  intro p _
  exact div_nonneg (sub_nonneg.mpr (Real.cos_le_one _)) (Nat.cast_nonneg p)

lemma bandPhase_le_phaseSum (t a : ℝ) (N : ℕ) (ha : 0 ≤ a) :
    bandPhase t a N ≤ phaseSum t N := by
  unfold bandPhase phaseSum
  rw [halasz_prime_band_tail N a ha]
  apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
  intro p _ _
  exact div_nonneg (sub_nonneg.mpr (Real.cos_le_one _)) (Nat.cast_nonneg p)

/-- Only the fixed prime 2 lies below exp(1). -/
lemma phaseSum_le_bandPhase (t : ℝ) (N : ℕ) :
    phaseSum t N ≤ bandPhase t (Real.exp 1) N + 1 := by
  have ha : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
  rw [bandPhase, halasz_prime_band_tail N (Real.exp 1) ha]
  have he := sum_filter_add_sum_filter_not (s := primesUpTo N)
    (f := fun p : ℕ => (1-Real.cos (t*Real.log (p : ℝ)))/(p : ℝ))
    (p := fun p : ℕ => Real.exp 1 < (p : ℝ))
  have hsmall : (primesUpTo N).filter (fun p : ℕ => ¬ Real.exp 1 < (p : ℝ)) ⊆ {2} := by
    intro p hp
    have hpr := (mem_filter.mp (mem_filter.mp hp).1).2
    have hpbound : (p : ℝ) < 3 :=
      (le_of_not_gt (mem_filter.mp hp).2).trans_lt Real.exp_one_lt_three
    have hp3 : p < 3 := by exact_mod_cast hpbound
    have hp2 := hpr.two_le
    simp only [mem_singleton]
    omega
  have hb := sum_le_sum_of_subset_of_nonneg
    (f := fun p : ℕ => (1-Real.cos (t*Real.log (p : ℝ)))/(p : ℝ))
    hsmall (fun p _ _ => div_nonneg (sub_nonneg.mpr (Real.cos_le_one _)) (Nat.cast_nonneg p))
  simp only [sum_singleton, Nat.cast_ofNat] at hb
  have hc := Real.neg_one_le_cos (t*Real.log 2)
  change _ + _ = phaseSum t N at he
  linarith only [he,hb,hc]

lemma bandPhase_exp_error : ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ,
    Real.exp 1 ≤ (N : ℝ) → ∀ t : ℝ, |t| ≤ 2 →
      |bandPhase t (Real.exp 1) N - oscillationIntegral t (Real.log N)| ≤ K := by
  obtain ⟨c,K,hc,hK,herr⟩ := modFiveThetaInput.halasz_prime_phase_error
  refine ⟨10*K,by positivity,?_⟩
  intro N hN t ht
  have hh := herr (Real.exp 1) N t le_rfl hN
  rw [halasz_log_phase_substitution _ _ _
    (Real.one_lt_exp_iff.mpr (by norm_num)) hN] at hh
  simp only [Real.log_exp] at hh
  change |bandPhase t (Real.exp 1) N - oscillationIntegral t (Real.log N)| ≤ _ at hh
  apply hh.trans
  have he : Real.exp (-c) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hp : (8+|t|)*K ≤ 10*K := mul_le_mul_of_nonneg_right (by linarith) hK
  norm_num only [Real.sqrt_one,div_one,mul_one] at hh ⊢
  apply (mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ (8+|t|)*K)).trans
  simpa only [mul_one] using hp

/-- Uniform comparison of the two prime phases in the small-height range. -/
theorem small_phase_difference : ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
    Real.exp 1 ≤ (N : ℝ) → ∀ t : ℝ, |t| ≤ 1 →
      phaseSum t N - phaseSum (2*t) N ≤ C := by
  obtain ⟨K,hK,herr⟩ := bandPhase_exp_error
  refine ⟨2*K+3,by positivity,?_⟩
  intro N hN t ht
  have hL : 1 ≤ Real.log (N : ℝ) := by
    have hl := Real.log_le_log (Real.exp_pos 1) hN
    simpa only [Real.log_exp] using hl
  have h1 := (abs_le.mp (herr N hN t (by linarith))).2
  have ht2 : |2*t| ≤ 2 := by rw [abs_mul]; norm_num; linarith
  have h2 := (abs_le.mp (herr N hN (2*t) ht2)).1
  have hi := oscillationIntegral_double t (Real.log N) hL
  have hhi := phaseSum_le_bandPhase t N
  have hlo := bandPhase_le_phaseSum (2*t) (Real.exp 1) N (Real.exp_pos 1).le
  linarith only [h1,h2,hi,hhi,hlo]

#print axioms small_phase_difference
end MRTRepulsion
