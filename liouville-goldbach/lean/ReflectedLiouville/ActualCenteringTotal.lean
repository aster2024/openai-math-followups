import ReflectedLiouville.ActualCentering
import ReflectedLiouville.FinalErrorDecay

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Filter
open scoped BigOperators Classical
open OAI.TwoPointCorrelations Finset

namespace ReflectedLiouville

/-- All actual bins, with the sharp linear bin count, have total centering
    cost at most a constant times the retained saving exp(-J). -/
theorem actual_centering_total (h_KMT : KMTInput) (h_MRT : MRTRealTwistRepulsionInput)
    (A : ℕ) (hA : 1000 ≤ A) (W : ℝ) (hW : 1 ≤ W) :
    ∃ C L₀ : ℝ, 0 < C ∧ 1 ≤ L₀ ∧ ∃ N₀ : ℕ, 3 ≤ N₀ ∧
      ∀ L : ℝ, L₀ ≤ L → ∀ (N : ℕ) [NeZero N], N₀ ≤ N → Real.log (N : ℝ) = L ^ A →
        ∀ (hL : 1 ≤ L),
          let J := reflectionBandCount W (1 / 100000) L
          let η := Real.exp (-(J : ℝ))
          let data := reflectionPrimeFamily N W (1 / 100000) L η hL (by linarith)
          let P := centeredPrimeBands N.primeFactors (L ^ (1-1/100000 : ℝ)) W J
          (∑ j ∈ paddingBinIndices L η,
            |centeredBinForm data.pairs N η j - rawBinForm data.pairs N η j|) ≤
              C * paddingTiltNormalizer data.Q * (∏ k, primeHarmonicMass (P k)) * η := by
  obtain ⟨C₁,L₁,hC₁,hL₁,N₀,hN₀,hb⟩ := actual_centering_bin_saving h_KMT h_MRT A hA W
    (1/100000) hW (by norm_num) (by norm_num)
  obtain ⟨L₂,hL₂⟩ := eventually_atTop.mp
    (eventually_reflectionBandCount_positive W (1/100000) (by linarith) (by norm_num))
  refine ⟨101*C₁,max L₁ L₂,by positivity,hL₁.trans (le_max_left _ _),N₀,hN₀,?_⟩
  intro L hL N inst hN hlog hLone
  dsimp only
  let J := reflectionBandCount W (1 / 100000) L
  let η := Real.exp (-(J : ℝ))
  let data := reflectionPrimeFamily N W (1 / 100000) L η hLone (by linarith : 0 ≤ W)
  let P := centeredPrimeBands N.primeFactors (L ^ (1-1/100000 : ℝ)) W J
  let S := paddingTiltNormalizer data.Q
  let V := ∏ k, primeHarmonicMass (P k)
  have hJ : 1 ≤ J := hL₂ L ((le_max_right _ _).trans hL)
  have hη : 0 < η := Real.exp_pos _
  have hηsmall : η ≤ 1/2 := by
    have hJr : (1 : ℝ) ≤ J := by exact_mod_cast hJ
    have hExp : (2 : ℝ) ≤ Real.exp (J : ℝ) := Real.exp_one_gt_two.le.trans (Real.exp_le_exp.mpr hJr)
    dsimp only [η]
    rw [Real.exp_neg]
    have hi := (inv_le_inv₀ (Real.exp_pos (J : ℝ)) (by norm_num : (0 : ℝ) < 2)).mpr hExp
    simpa only [one_div] using hi
  have hV : 0 ≤ V := by
    apply prod_nonneg
    intro k hk
    unfold primeHarmonicMass
    apply sum_nonneg
    intro p hp
    positivity
  have hS : 0 < S := paddingTiltNormalizer_pos _
  have hE : 0 ≤ (2 : ℝ)^J * S * V := by positivity
  have hBin := hb L ((le_max_left _ _).trans hL) N hN hlog hLone η hη hηsmall
  have hCard := paddingBinIndices_card_linear L η hLone hη (by linarith)
  have hTotal := sum_bin_log_saving (paddingBinIndices L η)
    (fun j => centeredBinForm data.pairs N η j - rawBinForm data.pairs N η j)
    L η C₁ ((2 : ℝ)^J * S * V) convolutionFinalExponent hLone hη hC₁.le hE hCard
    (fun j _ => by convert hBin j using 1 <;> ring)
  have hDecay : Real.exp (J : ℝ) * (2 : ℝ)^J * L ^ (-convolutionFinalExponent) ≤ η := by
    simpa only [convolutionFinalExponent,J,η,neg_div] using centering_error_decay W L hW hLone
  have hFinal := mul_le_mul_of_nonneg_left hDecay (by positivity : 0 ≤ 101*C₁*S*V)
  apply hTotal.trans
  dsimp only [η] at hFinal ⊢
  rw [Real.exp_neg] at hFinal ⊢
  simp only [div_eq_mul_inv,inv_inv]
  convert hFinal using 1 <;>
    simp only [S,V,P,data,η,J,Real.exp_neg,
      show (1-1/100000 : ℝ) = 99999/100000 by norm_num] <;> ring

#print axioms actual_centering_total
end ReflectedLiouville
