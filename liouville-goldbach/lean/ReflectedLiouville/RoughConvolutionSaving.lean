import ReflectedLiouville.QuotientConvolutionBound
import ReflectedLiouville.RoughConvolutionScales
import ReflectedLiouville.RoughMultiplier
import ReflectedLiouville.FourierWindowReduction

set_option autoImplicit false
set_option maxHeartbeats 800000
open Filter MeasureTheory
open scoped BigOperators Classical ComplexConjugate
open OAI.TwoPointCorrelations

namespace ReflectedLiouville

/-- The complete analytic rough reflected-convolution estimate: every
    Fourier and moment input is derived from KMT/MRT and proved library
    theorems. Only the actual support and scale conditions remain. -/
theorem reflected_rough_convolution_saving
    (h_KMT : KMTInput) (h_MRT : MRTRealTwistRepulsionInput) (A : ℕ) (hA : 1000 ≤ A) :
    ∃ C L₀ : ℝ, 0 < C ∧ 1 ≤ L₀ ∧ ∃ N₀ : ℕ, 3 ≤ N₀ ∧
      ∀ L : ℝ, L₀ ≤ L → ∀ N : ℕ, N₀ ≤ N → Real.log (N : ℝ) = L ^ A →
        ∀ (D : ℕ) (Y : ℝ),
          (1 / 2 : ℝ) * Real.exp (L ^ convolutionSizeExponent) ≤ (D : ℝ) →
          (D : ℝ) ≤ 2 * Real.exp (2 * L) → (N : ℝ) * D / 2 ≤ Y → Y / N ≤ (D : ℝ) →
          ∀ (Z : Finset ℕ) (c : ℕ → ℂ),
            (∀ z ∈ Z, D ≤ z ∧ z < D + D ∧ HasNoPrimeFactorBelow (Real.exp (L ^ convolutionRoughExponent)) z) →
            (∀ z ∈ Z, ‖c z‖ ≤ 1) →
            ‖∑ m ∈ Finset.Icc 1 ⌊Y⌋₊, ∑ v ∈ Z, (c v / (v : ℂ)) * liouville m * liouville (N * v - m)‖ / Y ≤
              C * L ^ (-1 - convolutionFinalExponent) := by
  have hAr : (0 : ℝ) < A := by exact_mod_cast (show 0 < A by omega)
  let ν := convolutionRoughExponent / A
  have hν : 0 < ν := by dsimp [ν, convolutionRoughExponent]; positivity
  have hν₁ : ν ≤ 1 := by
    dsimp only [ν]
    apply (div_le_one hAr).mpr
    have hAreal : (1000 : ℝ) ≤ A := by exact_mod_cast hA
    norm_num [convolutionRoughExponent]
    linarith
  obtain ⟨C₀, hC₀, N₀, hN₀, hprefix⟩ := quotient_circle_prefix_mean h_KMT h_MRT ν hν hν₁
  obtain ⟨U, V, hU, hV, hrough⟩ := rough_multiplier_with_slack
    convolutionRoughExponent convolutionSavingExponent convolutionSizeExponent
    (by norm_num [convolutionRoughExponent])
    (by norm_num [convolutionSavingExponent, convolutionRoughExponent])
    (by norm_num [convolutionRoughExponent, convolutionSizeExponent])
  have hevent := (eventually_rough_convolution_scales A hA).and (hrough.and (eventually_ge_atTop (1 : ℝ)))
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.mp hevent
  let C := 6 + 6 * (C₀ + 1) * U * V
  refine ⟨C, max 1 L₀, by dsimp [C]; positivity, le_max_left _ _, N₀, hN₀, ?_⟩
  intro L hL N hN hlog D Y hDlow hDhigh hYlow hYhigh Z c hZ hc
  obtain ⟨hscales, hroughL, hL1⟩ := hL₀ L ((le_max_right _ _).trans hL)
  have hN3 : 3 ≤ N := hN₀.trans hN
  have hn : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hn
  have hLp : 0 < L := by linarith
  have hDr : (0 : ℝ) < D := (by positivity : 0 < (1 / 2 : ℝ) * Real.exp (L ^ convolutionSizeExponent)).trans_le hDlow
  have hD1 : 1 ≤ D := by
    have hd : 0 < D := by exact_mod_cast hDr
    omega
  obtain ⟨hFlow, hFhigh, hRate, hDgain⟩ := hscales N hN3 hlog D Y hDlow hDhigh hYlow hYhigh
  have hprefixMean (θ : AddCircle (1 : ℝ)) := hprefix N hN Y hFlow hFhigh θ
  have hSource (θ : AddCircle (1 : ℝ)) : (∑ r : Fin N, ‖quotientSourcePolynomial N (r.val + 1) Y θ‖) ≤
      (C₀ + 1) * (N : ℝ) * D * L ^ (-convolutionFourierExponent) := by
    have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    have hD0one : 1 < Y / N :=
      (Real.one_lt_exp_iff.mpr (Real.rpow_pos_of_pos hlogN ν)).trans_le hFlow
    have hlogD0 : 0 < Real.log (Y / N) := Real.log_pos hD0one
    have hrecip : 1 / (Real.log (Y / N)) ^ (1 / 3000 : ℝ) ≤ L ^ (-convolutionFourierExponent) := by
      have ht := div_le_div_of_nonneg_left zero_le_one
        (Real.rpow_pos_of_pos hLp convolutionFourierExponent) hRate
      simpa only [one_div, Real.rpow_neg hLp.le] using ht
    have hterm : C₀ * (Y / N) / Real.rpow (Real.log (Y / N)) (1 / 3000) ≤
        C₀ * (D : ℝ) * L ^ (-convolutionFourierExponent) := by
      have hcpos : 0 ≤ C₀ * (Y / N) := by positivity
      have ht := mul_le_mul_of_nonneg_left hrecip hcpos
      have hhigh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hYhigh hC₀.le)
        (Real.rpow_nonneg hLp.le (-convolutionFourierExponent))
      have ht' : C₀ * (Y / N) / Real.rpow (Real.log (Y / N)) (1 / 3000) ≤
          C₀ * (Y / N) * L ^ (-convolutionFourierExponent) := by
        simp only [Real.rpow_eq_pow]
        convert ht using 1 <;> ring
      exact ht'.trans hhigh
    have hm := hprefixMean θ
    have hmean : (∑ r ∈ Finset.Icc 1 N, ‖quotientSourcePolynomial N r Y θ‖) / (N : ℝ) ≤
        (C₀ + 1) * D * L ^ (-convolutionFourierExponent) := by linarith only [hm, hterm, hDgain]
    rw [← sum_fin_shift_eq_Icc N (fun r => ‖quotientSourcePolynomial N r Y θ‖)] at hmean
    have ht := (div_le_iff₀ hNr).mp hmean
    convert ht using 1 <;> ring
  have hcbar : ∀ z ∈ Z, ‖conj (c z)‖ ≤ 1 := by
    intro z hz
    simpa only [Complex.norm_conj] using hc z hz
  obtain ⟨hSup, hFourth⟩ := hroughL D 1 hDlow (by decide) Z (fun z => conj (c z)) hZ hcbar
  have hNormB (θ : AddCircle (1 : ℝ)) : ‖meanPrimeMultiplier Z c θ‖ =
      ‖weightedRoughFourier Z (fun z => conj (c z)) 1 θ‖ := by
    rw [meanPrimeMultiplier_eq_conj]
    exact Complex.norm_conj _
  have hSup' : ∀ θ, ‖meanPrimeMultiplier Z c θ‖ ≤ U * L ^ (-convolutionSavingExponent) := by
    intro θ
    rw [hNormB]
    exact hSup θ
  have hFourth' : (∫ θ, ‖meanPrimeMultiplier Z c θ‖ ^ (4 : ℕ) ∂AddCircle.haarAddCircle) ≤
      V / D * L ^ (-4 * convolutionSavingExponent) := by
    simpa only [hNormB] using hFourth
  exact quotient_convolution_saving_from_bounds N D Y L (C₀ + 1) U V convolutionSavingExponent
    convolutionFourierExponent convolutionFinalExponent Z c hn hD1 hL1 hYlow hYhigh
    (fun z hz => by have := (hZ z hz).2.1; omega) (by positivity) hU.le hV.le
    (by norm_num [convolutionSavingExponent, convolutionFourierExponent, convolutionFinalExponent])
    hSource hSup' hFourth'

#print axioms reflected_rough_convolution_saving

end ReflectedLiouville
