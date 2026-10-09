import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCosineLower

set_option autoImplicit false
open MeasureTheory
open OAI.TwoPointCorrelations

namespace MRTRepulsion

noncomputable def oscillationIntegral (t L : ℝ) : ℝ :=
  ∫ y in (1 : ℝ)..L, (1 - Real.cos (t*y))/y

lemma oscillation_integrable (t a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun y : ℝ => (1 - Real.cos (t*y))/y) volume a b := by
  apply ContinuousOn.intervalIntegrable_of_Icc hab
  intro y hy
  have hn : y ≠ 0 := (ha.trans_le hy.1).ne'
  exact (by fun_prop (disch := assumption) :
    ContinuousAt (fun y : ℝ => (1 - Real.cos (t*y))/y) y).continuousWithinAt

/-- Doubling the frequency shifts the integration interval. The lost initial
    interval has an absolute bound, and the terminal interval is nonnegative. -/
lemma oscillationIntegral_double (t L : ℝ) (hL : 1 ≤ L) :
    oscillationIntegral t L - oscillationIntegral (2*t) L ≤ 2 := by
  let g : ℝ → ℝ := fun y => (1 - Real.cos (t*y))/y
  have h12 := oscillation_integrable t 1 2 (by norm_num) (by norm_num)
  have h1L := oscillation_integrable t 1 L (by norm_num) hL
  have hL2L := oscillation_integrable t L (2*L) (by linarith) (by linarith)
  have h22L := oscillation_integrable t 2 (2*L) (by norm_num) (by linarith)
  have hs := intervalIntegral.integral_comp_mul_left (a := 1) (b := L) (c := 2)
    g (by norm_num)
  have hscale : oscillationIntegral (2*t) L = ∫ y in (2 : ℝ)..2*L, g y := by
    have he : oscillationIntegral (2*t) L = 2 * ∫ y in (1 : ℝ)..L, g (2*y) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro y _
      dsimp [g]
      rw [show (2*t)*y = t*(2*y) by ring]
      simp only [div_eq_mul_inv,mul_inv_rev]
      norm_num
      ring
    rw [he,hs]
    simp
  have ha := intervalIntegral.integral_add_adjacent_intervals h1L hL2L
  have hb := intervalIntegral.integral_add_adjacent_intervals h12 h22L
  have htail : 0 ≤ ∫ y in L..2*L, g y :=
    logarithmic_oscillation_nonneg t L (2*L) (by linarith) (by linarith)
  have hhead : (∫ y in (1 : ℝ)..2, g y) ≤ 2 := by
    have hi : IntervalIntegrable (fun y : ℝ => 2/y) volume 1 2 := by
      apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num : (1 : ℝ) ≤ 2)
      intro y hy
      have hn : y ≠ 0 := by linarith [hy.1]
      exact (continuousAt_const.div continuousAt_id hn).continuousWithinAt
    have hm := intervalIntegral.integral_mono_on (by norm_num : (1 : ℝ) ≤ 2)
      h12 hi (fun y hy => div_le_div_of_nonneg_right
        (by linarith [Real.neg_one_le_cos (t*y)] : 1-Real.cos (t*y) ≤ 2)
        (by linarith [hy.1] : 0 ≤ y))
    have he : (∫ y in (1 : ℝ)..2, 2/y) = 2*Real.log 2 := by
      simp_rw [show ∀ y : ℝ, 2/y = 2*(1/y) from fun y => by ring]
      rw [intervalIntegral.integral_const_mul, integral_one_div_of_pos (by norm_num) (by norm_num)]
      norm_num
    rw [he] at hm
    exact hm.trans (by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)])
  rw [hscale]
  change (∫ y in (1 : ℝ)..L, g y) - _ ≤ 2
  change (∫ y in (1 : ℝ)..L, g y) + (∫ y in L..2*L, g y) = _ at ha
  change (∫ y in (1 : ℝ)..2, g y) + (∫ y in (2 : ℝ)..2*L, g y) = _ at hb
  linarith only [ha,hb,htail,hhead]

#print axioms oscillationIntegral_double
end MRTRepulsion
