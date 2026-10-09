import ReflectedLiouville.CenteringMomentBound

set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Classical

namespace ReflectedLiouville

noncomputable def circleNormProductSum {ι : Type*} [Fintype ι]
    (F G : ι → AddCircle (1 : ℝ) → ℂ) (θ : AddCircle (1 : ℝ)) : ℝ :=
  ∑ i, ‖F i θ‖ * ‖G i θ‖

lemma circleNormProductSum_nonneg {ι : Type*} [Fintype ι]
    (F G : ι → AddCircle (1 : ℝ) → ℂ) (θ : AddCircle (1 : ℝ)) :
    0 ≤ circleNormProductSum F G θ := Finset.sum_nonneg (fun i _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))

lemma circleNormProductSum_continuous {ι : Type*} [Fintype ι]
    (F G : ι → AddCircle (1 : ℝ) → ℂ) (hF : ∀ i, Continuous (F i)) (hG : ∀ i, Continuous (G i)) :
    Continuous (circleNormProductSum F G) :=
  continuous_finsetSum _ (fun i _ => (hF i).norm.mul (hG i).norm)

/-- The finite triple-convolution estimate with all product integrability
    discharged by continuity on the compact circle. -/
theorem circle_convolution_moment_bound {ι : Type*} [Fintype ι]
    (F G : ι → AddCircle (1 : ℝ) → ℂ) (B : AddCircle (1 : ℝ) → ℂ)
    (hF : ∀ i, Continuous (F i)) (hG : ∀ i, Continuous (G i)) (hB : Continuous B)
    (L N D Y C U V γ β s : ℝ)
    (hL : 1 ≤ L) (hN : 0 < N) (hD : 0 < D) (hY : N * D / 2 ≤ Y)
    (hC : 0 ≤ C) (hU : 0 ≤ U) (hV : 0 ≤ V) (hmargin : 5 + 5 * s ≤ 5 * γ + β)
    (hPoint : ∀ θ, circleNormProductSum F G θ ≤ 3 * C * N * D ^ (2 : ℕ) * L ^ (-β))
    (hSup : ∀ θ, ‖B θ‖ ≤ U * L ^ (-γ))
    (hEnergy : (∫ θ, circleNormProductSum F G θ ∂AddCircle.haarAddCircle) ≤ 3 * N * D)
    (hFourth : (∫ θ, ‖B θ‖ ^ (4 : ℕ) ∂AddCircle.haarAddCircle) ≤ V / D * L ^ (-4 * γ)) :
    ‖∑ i, ∫ θ, F i θ * G i θ * B θ ∂AddCircle.haarAddCircle‖ / Y ≤
      (6 + 6 * C * U * V) * L ^ (-1 - s) := by
  let H := circleNormProductSum F G
  have hH := circleNormProductSum_continuous F G hF hG
  have hNormInt (i : ι) : Integrable (fun θ => ‖F i θ‖ * ‖G i θ‖ * ‖B θ‖) AddCircle.haarAddCircle :=
    continuous_circle_real_integrable _ (((hF i).norm.mul (hG i).norm).mul hB.norm)
  have hbound : ‖∑ i, ∫ θ, F i θ * G i θ * B θ ∂AddCircle.haarAddCircle‖ ≤
      ∫ θ, H θ * ‖B θ‖ ∂AddCircle.haarAddCircle := by
    calc
      _ ≤ ∑ i, ‖∫ θ, F i θ * G i θ * B θ ∂AddCircle.haarAddCircle‖ := norm_sum_le _ _
      _ ≤ ∑ i, ∫ θ, ‖F i θ‖ * ‖G i θ‖ * ‖B θ‖ ∂AddCircle.haarAddCircle := by
        apply Finset.sum_le_sum
        intro i hi
        simpa only [norm_mul] using norm_integral_le_integral_norm (fun θ => F i θ * G i θ * B θ)
      _ = ∫ θ, ∑ i, ‖F i θ‖ * ‖G i θ‖ * ‖B θ‖ ∂AddCircle.haarAddCircle := by
        rw [integral_finsetSum _ (fun i _ => hNormInt i)]
      _ = _ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun θ => by dsimp only [H, circleNormProductSum]; rw [Finset.sum_mul])
  have hMoment := centering_convolution_bound_from_moments H B L N D Y C U V γ β s
    hL hN hD hY hC hU hV hmargin (circleNormProductSum_nonneg F G) hPoint hSup
    (continuous_circle_real_integrable _ hH)
    (continuous_circle_real_integrable _ (hB.norm.pow 4))
    (continuous_circle_real_integrable _ (hH.mul hB.norm)) hEnergy hFourth
  have hYpos : 0 < Y := (by positivity : 0 < N * D / 2).trans_le hY
  exact (div_le_div_of_nonneg_right hbound hYpos.le).trans hMoment

#print axioms circle_convolution_moment_bound

end ReflectedLiouville
