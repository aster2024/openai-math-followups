import ReflectedLiouville.KeptBadDecay
import ReflectedLiouville.FinalErrorDecay

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Filter
open scoped BigOperators Classical
open OAI.TwoPointCorrelations Finset

namespace ReflectedLiouville

theorem actual_kept_total :
    ∃ Af : ℕ, 1000 ≤ Af ∧ ∀ a : ℝ, ∀ᶠ L : ℝ in atTop,
      ∀ (N : ℕ) [NeZero N], Real.log (N : ℝ) ≤ L ^ a → Real.exp (L ^ Af / 2) ≤ (N : ℝ) →
        ∀ (hL : 1 ≤ L),
          let W := (10 : ℝ)^(180 : ℕ)
          let J := reflectionBandCount W (1/100000) L
          let η := Real.exp (-(J : ℝ))
          let data := reflectionPrimeFamily N W (1/100000) L η hL (by positivity)
          let P := centeredPrimeBands N.primeFactors (L ^ (1-1/100000 : ℝ)) W J
          (∑ j ∈ paddingBinIndices L η, |keptCenteredBinForm data L W η j|) ≤
            405 * paddingTiltNormalizer data.Q * (∏ k, primeHarmonicMass (P k)) * η := by
  let W := (10 : ℝ)^(180 : ℕ)
  have hW : 1 ≤ W := by dsimp only [W]; norm_num
  obtain ⟨Af,hAf,hb⟩ := actual_kept_bin_bound W (1/100000) hW (by norm_num) (by norm_num)
  refine ⟨Af,hAf,?_⟩
  intro a
  filter_upwards [hb a,eventually_reflection_pool_range a W (1/100000) hW (by norm_num) (by norm_num),
    eventually_kept_bad_decay W (1/100000) hW (by norm_num) (by norm_num),
    eventually_ge_atTop (2 : ℝ)] with L hbound hpool hbad hLtwo
  intro N inst hNlog hLength hLone
  dsimp only
  let J := reflectionBandCount W (1/100000) L
  let η := Real.exp (-(J : ℝ))
  let data := reflectionPrimeFamily N W (1/100000) L η hLone (by positivity : 0 ≤ W)
  let P := centeredPrimeBands N.primeFactors (L ^ (1-1/100000 : ℝ)) W J
  let S := paddingTiltNormalizer data.Q
  let V := ∏ k, primeHarmonicMass (P k)
  let B := Real.exp (4*J) * (((3 : ℝ)^(170 : ℕ))*Real.sqrt W)^J
  let E := Real.exp (4*J) * (8*W)^J * (5 : ℝ)^(400*Real.log L) * Real.exp (-(2*⌊L⌋₊ : ℕ))
  have hrange := hpool N hNlog hLone η
  have hVone : 1 ≤ V := by
    calc
      _ = ∏ _k : Fin J, (1 : ℝ) := by simp
      _ ≤ _ := prod_le_prod₀ (fun _ _ => zero_le_one) (fun k _ => hW.trans (hrange.bandsLower k))
  have hWV : W^J ≤ V := by
    calc
      _ = ∏ _k : Fin J, W := by simp
      _ ≤ _ := prod_le_prod₀ (fun _ _ => by linarith) (fun k _ => hrange.bandsLower k)
  have hSone : 1 ≤ S := paddingTiltNormalizer_one_le _
  have hS : 0 < S := paddingTiltNormalizer_pos _
  have hV : 0 < V := by linarith
  have hη : 0 < η := Real.exp_pos _
  have hηone : η ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Nat.cast_nonneg _))
  have hLpos : 0 < L := by linarith
  have hCard := paddingBinIndices_card_linear L η hLone hη hηone
  have hsum : (∑ j ∈ paddingBinIndices L η, |keptCenteredBinForm data L W η j|) ≤
      (paddingBinIndices L η).card * (4*S/L*B + 4*E/L) := by
    apply (sum_le_sum (hbound N hNlog hLength hLone)).trans_eq
    simp only [sum_const,nsmul_eq_mul]
    dsimp only [S,B,E,data,η,J]
    ring
  have hCost : (∑ j ∈ paddingBinIndices L η, |keptCenteredBinForm data L W η j|) ≤
      404*S*B/η + 404*E/η := by
    apply hsum.trans
    have hc := mul_le_mul_of_nonneg_right hCard
      (by dsimp only [B,E]; positivity : 0 ≤ 4*S/L*B + 4*E/L)
    convert hc using 1 <;> field_simp <;> ring
  have hsqrt : 0 < Real.sqrt W := Real.sqrt_pos.mpr (by linarith)
  have hratio : (((3 : ℝ)^(170 : ℕ))*Real.sqrt W)^J ≤
      V * (((3 : ℝ)^(170 : ℕ))/Real.sqrt W)^J := by
    have he : W * (((3 : ℝ)^(170 : ℕ))/Real.sqrt W) = ((3 : ℝ)^(170 : ℕ))*Real.sqrt W := by
      field_simp
      nlinarith [Real.sq_sqrt (by linarith : 0 ≤ W)]
    have hm := mul_le_mul_of_nonneg_right hWV
      (by positivity : 0 ≤ (((3 : ℝ)^(170 : ℕ))/Real.sqrt W)^J)
    rw [← mul_pow,he] at hm
    exact hm
  have hGood : S*B/η ≤ S*V*η := by
    have hSpec := spectral_error_decay J
    have hnum := mul_le_mul_of_nonneg_left hratio (Real.exp_pos (5*J)).le
    have hscale : Real.exp (4*J)/η = Real.exp (5*J) := by
      dsimp only [η]
      rw [Real.exp_neg,div_eq_mul_inv,inv_inv,← Real.exp_add]
      congr 1
      ring
    have hM := mul_le_mul_of_nonneg_left hSpec hV.le
    have ht : Real.exp (5*J) * (((3 : ℝ)^(170 : ℕ))*Real.sqrt W)^J ≤ V*η := by
      apply hnum.trans
      convert hM using 1 <;> ring
    have hs := mul_le_mul_of_nonneg_left ht hS.le
    have hid : S*B/η = S*Real.exp (5*J)*(((3 : ℝ)^(170 : ℕ))*Real.sqrt W)^J := by
      dsimp only [B]
      calc
        _ = S*(Real.exp (4*J)/η)*(((3 : ℝ)^(170 : ℕ))*Real.sqrt W)^J := by ring
        _ = _ := by rw [hscale]
    rw [hid]
    convert hs using 1 <;> ring
  have hBad : 404*E/η ≤ η := by
    have he : 404*E/η = 404*Real.exp (5*J)*(8*W)^J*(5 : ℝ)^(400*Real.log L)*
        Real.exp (-(2*⌊L⌋₊ : ℕ)) := by
      dsimp only [E,η]
      rw [Real.exp_neg (J : ℝ),div_eq_mul_inv,inv_inv]
      have hh : Real.exp (4*J)*Real.exp (J : ℝ) = Real.exp (5*J) := by rw [← Real.exp_add]; congr 1; ring
      calc
        _ = 404*(Real.exp (4*J)*Real.exp (J : ℝ))*(8*W)^J*(5 : ℝ)^(400*Real.log L)*
          Real.exp (-(2*⌊L⌋₊ : ℕ)) := by ring
        _ = _ := by rw [hh]
    rw [he]
    exact hbad
  have hSV : 1 ≤ S*V := by
    simpa only [one_mul] using mul_le_mul hSone hVone zero_le_one hS.le
  have hBadSV : η ≤ S*V*η := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hSV hη.le
  have hGood404 := mul_le_mul_of_nonneg_left hGood (by norm_num : (0 : ℝ) ≤ 404)
  change (∑ j ∈ paddingBinIndices L η, |keptCenteredBinForm data L W η j|) ≤ 405*S*V*η
  have hGood404' : 404*S*B/η ≤ 404*S*V*η := by convert hGood404 using 1 <;> ring
  calc
    _ ≤ 404*S*B/η + 404*E/η := hCost
    _ ≤ 404*S*V*η + S*V*η := add_le_add hGood404' (hBad.trans hBadSV)
    _ = _ := by ring

#print axioms actual_kept_total
end ReflectedLiouville
