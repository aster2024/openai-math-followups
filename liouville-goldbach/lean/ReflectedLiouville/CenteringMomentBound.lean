import ReflectedLiouville.ConvolutionThreshold
import ReflectedLiouville.CirclePolynomialEnergy

set_option autoImplicit false
open MeasureTheory

namespace ReflectedLiouville

/-- The quantitative centering exponent calculation, from the three actual
    polynomial moments. Every integral has an explicit integrability proof. -/
theorem centering_convolution_bound_from_moments
    (H : AddCircle (1 : ℝ) → ℝ) (B : AddCircle (1 : ℝ) → ℂ)
    (L N D Y C U V γ β s : ℝ)
    (hL : 1 ≤ L) (hN : 0 < N) (hD : 0 < D) (hY : N * D / 2 ≤ Y)
    (hC : 0 ≤ C) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hmargin : 5 + 5 * s ≤ 5 * γ + β)
    (hH : ∀ θ, 0 ≤ H θ)
    (hHM : ∀ θ, H θ ≤ 3 * C * N * D ^ (2 : ℕ) * L ^ (-β))
    (hSup : ∀ θ, ‖B θ‖ ≤ U * L ^ (-γ))
    (hIntH : Integrable H AddCircle.haarAddCircle)
    (hIntB : Integrable (fun θ => ‖B θ‖ ^ (4 : ℕ)) AddCircle.haarAddCircle)
    (hIntProduct : Integrable (fun θ => H θ * ‖B θ‖) AddCircle.haarAddCircle)
    (hEnergy : (∫ θ, H θ ∂AddCircle.haarAddCircle) ≤ 3 * N * D)
    (hFourth : (∫ θ, ‖B θ‖ ^ (4 : ℕ) ∂AddCircle.haarAddCircle) ≤ V / D * L ^ (-4 * γ)) :
    (∫ θ, H θ * ‖B θ‖ ∂AddCircle.haarAddCircle) / Y ≤
      (6 + 6 * C * U * V) * L ^ (-1 - s) := by
  have hLp : 0 < L := by linarith
  have hND : 0 < N * D / 2 := by positivity
  have hYp : 0 < Y := hND.trans_le hY
  let t := L ^ (-1 - s)
  let a := L ^ (-β)
  let b := L ^ (-γ)
  let c := L ^ (-4 * γ)
  let p := 4 * (1 + s) - 5 * γ - β
  have ht : 0 < t := Real.rpow_pos_of_pos hLp _
  have ha : 0 ≤ a := Real.rpow_nonneg hLp.le _
  have hb : 0 ≤ b := Real.rpow_nonneg hLp.le _
  have hc : 0 ≤ c := Real.rpow_nonneg hLp.le _
  have hbound := convolution_threshold_of_moments AddCircle.haarAddCircle H B
    (3 * C * N * D ^ (2 : ℕ) * a) (U * b) t (3 * N * D) (V / D * c) Y
    hH hHM (by positivity) (by positivity) ht hYp hSup hIntH hIntB hIntProduct hEnergy hFourth
  let num := t * (3 * N * D) + ((3 * C * N * D ^ (2 : ℕ) * a) * (U * b) / t ^ (4 : ℕ)) * (V / D * c)
  have hnum : 0 ≤ num := by dsimp [num]; positivity
  have hden := div_le_div_of_nonneg_left hnum hND hY
  have hpower : a * b * c / t ^ (4 : ℕ) = L ^ p := by
    dsimp only [a, b, c, t, p]
    rw [← Real.rpow_mul_natCast hLp.le, ← Real.rpow_add hLp, ← Real.rpow_add hLp, ← Real.rpow_sub hLp]
    congr 1
    ring
  have halgebra : num / (N * D / 2) = 6 * t + 6 * C * U * V * (a * b * c / t ^ (4 : ℕ)) := by
    dsimp only [num]
    field_simp [hN.ne', hD.ne', ht.ne']
    <;> ring
  have hexp : p ≤ -1 - s := by dsimp [p]; linarith
  have hp : L ^ p ≤ t := Real.rpow_le_rpow_of_exponent_le hL hexp
  have hcoef : 0 ≤ 6 * C * U * V := by positivity
  calc
    _ ≤ num / Y := hbound
    _ ≤ num / (N * D / 2) := hden
    _ = 6 * t + 6 * C * U * V * L ^ p := by rw [halgebra, hpower]
    _ ≤ 6 * t + 6 * C * U * V * t := by
      have hmul := mul_le_mul_of_nonneg_left hp hcoef
      linarith only [hmul]
    _ = _ := by dsimp only [t]; ring

lemma centering_slack_exponent_valid :
    (5 : ℝ) + 5 * (1 / 100000) ≤ 5 * (99997 / 100000) + 1 / 4000 := by norm_num

#print axioms centering_convolution_bound_from_moments

end ReflectedLiouville
