import RealCharacterTail.FiniteContour
import RealCharacterTail.RightTail
import RealCharacterTail.Smoothing

set_option autoImplicit false
open scoped Topology
open Set Filter MeasureTheory Complex Erdos970
open OAI.TwoPointCorrelations

namespace RealCharacterTail

/-- Exact decomposition of the Perron integral after subtracting its value at one. -/
theorem smoothed_decomposition {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (H : ℂ → ℂ)
    (hHd : DifferentiableOn ℂ H {s | (7 / 8 : ℝ) < s.re})
    (hEuler : ∀ s : ℂ, 1 < s.re → H s = LSeries (logCoeff χ) s)
    {x : ℝ} (hx : 1 < x) :
    smoothedReciprocalSum χ x = H 1 * (1 - 1 / (x : ℂ)) +
      VerticalIntegral' (removedIntegrand H x) 2 := by
  have hxp : 0 < x := zero_lt_one.trans hx
  have hk : Integrable (fun t : ℝ => modFivePerronKernel x ((2 : ℂ) + (t : ℂ) * Complex.I)) := by
    simpa using modFivePerronKernel_integrable (σ := (2 : ℝ)) hxp (by norm_num)
  have hg := removed_right_integrable χ H hHd hEuler hxp
  have heq : ∀ t : ℝ,
      LSeries (logCoeff χ) (((2 : ℂ) + (t : ℂ) * Complex.I) + 1) *
          modFivePerronKernel x ((2 : ℂ) + (t : ℂ) * Complex.I) =
        H 1 * modFivePerronKernel x ((2 : ℂ) + (t : ℂ) * Complex.I) +
          removedIntegrand H x ((2 : ℂ) + (t : ℂ) * Complex.I) := by
    intro t
    have hs0 : (2 : ℂ) + (t : ℂ) * Complex.I ≠ 0 := by
      intro he
      have := congrArg Complex.re he
      norm_num at this
    rw [← hEuler _ (by norm_num), removedIntegrand_eq H x hs0]
    rw [add_comm ((2 : ℂ) + (t : ℂ) * Complex.I) 1]
    ring
  have hv : VerticalIntegral' (fun s => LSeries (logCoeff χ) (s + 1) * modFivePerronKernel x s) 2 =
      H 1 * VerticalIntegral' (modFivePerronKernel x) 2 +
        VerticalIntegral' (removedIntegrand H x) 2 := by
    simp only [VerticalIntegral', VerticalIntegral, smul_eq_mul]
    push_cast
    have hi : (∫ t : ℝ, LSeries (logCoeff χ) (((2 : ℂ) + (t : ℂ) * Complex.I) + 1) *
        modFivePerronKernel x ((2 : ℂ) + (t : ℂ) * Complex.I)) =
      ∫ t : ℝ, H 1 * modFivePerronKernel x ((2 : ℂ) + (t : ℂ) * Complex.I) +
        removedIntegrand H x ((2 : ℂ) + (t : ℂ) * Complex.I) :=
      integral_congr_ae (Filter.Eventually.of_forall heq)
    rw [hi, integral_add (hk.const_mul (H 1)) hg, integral_const_mul]
    ring
  rw [smoothedReciprocalSum_perron χ hxp, hv,
    modFivePerron_gt_one (σ := (2 : ℝ)) hx (by norm_num)]

/-- Finite-height approximation to the normalized logarithm at one. -/
theorem smoothed_approximation_bound {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (H : ℂ → ℂ)
    (hHd : DifferentiableOn ℂ H {s | (7 / 8 : ℝ) < s.re})
    (hExp : ∀ s : ℂ, (7 / 8 : ℝ) < s.re → Complex.exp (H s) = χ.LFunction s)
    (hEuler : ∀ s : ℂ, 1 < s.re → H s = LSeries (logCoeff χ) s)
    {x T : ℝ} (hx : 2 ≤ x) (hT : 1 ≤ T) :
    ‖smoothedReciprocalSum χ x - H 1‖ ≤
      ‖H 1‖ / x +
        500000 * (Real.log (20 * (q : ℝ) * (T + 2)) + 1) *
          (x ^ (-1 / 16 : ℝ) + x ^ 2 / T ^ 2) +
        2 * (3 / 2 + ‖H 1‖) * x ^ 2 / T := by
  have hxp : 0 < x := by linarith
  have hTp : 0 < T := by linarith
  have hf := finite_contour_bound χ hχ H hHd hExp hEuler (by linarith : 1 ≤ x) hT
  have ht := removed_right_tail_bound χ H hHd hEuler hxp hTp
  have hv : ‖VerticalIntegral (removedIntegrand H x) 2‖ ≤
      ‖VIntegral (removedIntegrand H x) 2 (-T) T‖ +
        2 * (3 / 2 + ‖H 1‖) * x ^ 2 / T := by
    have hn := norm_le_norm_sub_add
      (VerticalIntegral (removedIntegrand H x) 2) (VIntegral (removedIntegrand H x) 2 (-T) T)
    linarith
  have hnormalized : ‖VerticalIntegral' (removedIntegrand H x) 2‖ ≤
      ‖VerticalIntegral (removedIntegrand H x) 2‖ := by
    rw [VerticalIntegral', norm_smul]
    exact mul_le_of_le_one_left (norm_nonneg _) modFive_perron_normalization
  rw [smoothed_decomposition χ H hHd hEuler (by linarith : 1 < x)]
  have he : H 1 * (1 - 1 / (x : ℂ)) + VerticalIntegral' (removedIntegrand H x) 2 - H 1 =
      VerticalIntegral' (removedIntegrand H x) 2 - H 1 / (x : ℂ) := by ring
  rw [he]
  have hn := norm_sub_le (VerticalIntegral' (removedIntegrand H x) 2) (H 1 / (x : ℂ))
  have hc : ‖H 1 / (x : ℂ)‖ = ‖H 1‖ / x := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hxp]
  rw [hc] at hn
  linarith

#print axioms smoothed_decomposition
#print axioms smoothed_approximation_bound

end RealCharacterTail
