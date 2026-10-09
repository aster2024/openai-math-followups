import RealCharacterTail.ContourKernel

set_option autoImplicit false
open scoped Topology
open Set Filter MeasureTheory Complex Erdos970
open OAI.TwoPointCorrelations

namespace RealCharacterTail

lemma removed_right_point_bound {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (H : ℂ → ℂ)
    (hEuler : ∀ s : ℂ, 1 < s.re → H s = LSeries (logCoeff χ) s)
    (x t : ℝ) :
    ‖removedIntegrand H x ((2 : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      (3 / 2 + ‖H 1‖) * ‖modFivePerronKernel x ((2 : ℂ) + (t : ℂ) * Complex.I)‖ := by
  have hs0 : (2 : ℂ) + (t : ℂ) * Complex.I ≠ 0 := by
    intro he
    have := congrArg Complex.re he
    norm_num at this
  have he : 1 + ((2 : ℂ) + (t : ℂ) * Complex.I) = (3 : ℂ) + (t : ℂ) * Complex.I := by ring
  rw [removedIntegrand_eq H x hs0, norm_mul, he]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply (norm_sub_le _ _).trans
  apply add_le_add _ le_rfl
  rw [hEuler _ (by simp)]
  exact norm_logEuler_three_le χ t

lemma removed_right_integrable {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (H : ℂ → ℂ)
    (hHd : DifferentiableOn ℂ H {s | (7 / 8 : ℝ) < s.re})
    (hEuler : ∀ s : ℂ, 1 < s.re → H s = LSeries (logCoeff χ) s)
    {x : ℝ} (hx : 0 < x) :
    Integrable (fun t : ℝ => removedIntegrand H x ((2 : ℂ) + (t : ℂ) * Complex.I)) := by
  have hc : Continuous (fun t : ℝ => removedIntegrand H x ((2 : ℂ) + (t : ℂ) * Complex.I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hUo : IsOpen {s : ℂ | (-1 / 8 : ℝ) < s.re} :=
      Complex.continuous_re.isOpen_preimage _ isOpen_Ioi
    have hs : (2 : ℂ) + (t : ℂ) * Complex.I ∈ {s : ℂ | (-1 / 8 : ℝ) < s.re} := by norm_num
    have hline : ContinuousAt (fun u : ℝ => (2 : ℂ) + (u : ℂ) * Complex.I) t := by fun_prop
    exact ((removedIntegrand_differentiableOn H hHd hx).differentiableAt
      (hUo.mem_nhds hs)).continuousAt.comp (f := fun u : ℝ => (2 : ℂ) + (u : ℂ) * Complex.I) hline
  have hi : Integrable (fun t : ℝ =>
      (3 / 2 + ‖H 1‖) * (4 * x ^ (2 : ℝ) / (1 + t ^ 2))) := by
    simpa only [div_eq_mul_inv, mul_assoc] using
      (integrable_inv_one_add_sq.const_mul ((3 / 2 + ‖H 1‖) * (4 * x ^ (2 : ℝ))))
  apply hi.mono' hc.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun t =>
    (removed_right_point_bound χ H hEuler x t).trans
      (mul_le_mul_of_nonneg_left (modFive_perron_kernel_vertical hx (by norm_num) t)
        (by positivity))

/-- The right vertical tail needs no bound growing with the height. -/
theorem removed_right_tail_bound {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (H : ℂ → ℂ)
    (hHd : DifferentiableOn ℂ H {s | (7 / 8 : ℝ) < s.re})
    (hEuler : ∀ s : ℂ, 1 < s.re → H s = LSeries (logCoeff χ) s)
    {x T : ℝ} (hx : 0 < x) (hT : 0 < T) :
    ‖VerticalIntegral (removedIntegrand H x) 2 - VIntegral (removedIntegrand H x) 2 (-T) T‖ ≤
      2 * (3 / 2 + ‖H 1‖) * x ^ 2 / T := by
  have hi := removed_right_integrable χ H hHd hEuler hx
  have ht := modFive_vertical_tails (σ := (2 : ℝ)) hT hi (D := (3 / 2 + ‖H 1‖) * x ^ 2) ?_
  · simpa only [mul_assoc] using ht
  intro t ht
  have ht0 : t ≠ 0 := by intro he; simp [he] at ht; linarith
  apply (removed_right_point_bound χ H hEuler x t).trans
  apply (mul_le_mul_of_nonneg_left (modFive_perron_kernel_horizontal hx 2 ht0)
    (by positivity : 0 ≤ 3 / 2 + ‖H 1‖)).trans_eq
  rw [Real.rpow_two]
  ring

#print axioms removed_right_tail_bound

end RealCharacterTail
