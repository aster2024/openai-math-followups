import RealCharacterTail.ContourKernel

set_option autoImplicit false
open scoped Topology
open Set Filter MeasureTheory Complex Erdos970
open OAI.TwoPointCorrelations

namespace RealCharacterTail

/-- Uniform finite-height estimate for the integrand after subtraction. -/
theorem removedIntegrand_point_bound {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (H : ℂ → ℂ)
    (hHd : DifferentiableOn ℂ H {s | (7 / 8 : ℝ) < s.re})
    (hExp : ∀ s : ℂ, (7 / 8 : ℝ) < s.re → Complex.exp (H s) = χ.LFunction s)
    (hEuler : ∀ s : ℂ, 1 < s.re → H s = LSeries (logCoeff χ) s)
    {σ t T : ℝ} (hσ : -1 / 16 ≤ σ) (hσ2 : σ ≤ 2) (ht : |t| ≤ T)
    (hs0 : (σ : ℂ) + (t : ℂ) * Complex.I ≠ 0) (x : ℝ) :
    ‖removedIntegrand H x ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      400 * (Real.log (20 * (q : ℝ) * (T + 2)) + 1) *
        ‖modFivePerronKernel x ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by
  have hT : 0 ≤ T := (abs_nonneg t).trans ht
  have h1 := norm_log_height_bound χ hχ H hHd hExp hEuler
    (σ := 1) (t := 0) (T := T) (by norm_num) (by norm_num) (by simpa using hT)
  have hz := norm_log_height_bound χ hχ H hHd hExp hEuler
    (σ := 1 + σ) (t := t) (T := T) (by linarith) (by linarith) ht
  have heq : (((1 + σ : ℝ) : ℂ) + (t : ℂ) * Complex.I) =
      1 + ((σ : ℂ) + (t : ℂ) * Complex.I) := by push_cast; ring
  rw [heq] at hz
  simp only [Complex.ofReal_one, Complex.ofReal_zero, zero_mul, add_zero] at h1
  have hdiff := (norm_sub_le (H (1 + ((σ : ℂ) + (t : ℂ) * Complex.I))) (H 1)).trans
    (add_le_add hz h1)
  rw [removedIntegrand_eq H x hs0, norm_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  linarith

/-- A finite rectangle shift, with absolute numerical constants. -/
theorem finite_contour_bound {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (H : ℂ → ℂ)
    (hHd : DifferentiableOn ℂ H {s | (7 / 8 : ℝ) < s.re})
    (hExp : ∀ s : ℂ, (7 / 8 : ℝ) < s.re → Complex.exp (H s) = χ.LFunction s)
    (hEuler : ∀ s : ℂ, 1 < s.re → H s = LSeries (logCoeff χ) s)
    {x T : ℝ} (hx : 1 ≤ x) (hT : 1 ≤ T) :
    ‖VIntegral (removedIntegrand H x) 2 (-T) T‖ ≤
      500000 * (Real.log (20 * (q : ℝ) * (T + 2)) + 1) *
        (x ^ (-1 / 16 : ℝ) + x ^ 2 / T ^ 2) := by
  let B : ℝ := Real.log (20 * (q : ℝ) * (T + 2)) + 1
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hBlog : 0 ≤ Real.log (20 * (q : ℝ) * (T + 2)) := by
    apply Real.log_nonneg
    nlinarith [mul_le_mul_of_nonneg_right hq1 (by linarith : 0 ≤ T + 2)]
  have hB : 0 ≤ B := by dsimp [B]; linarith
  have hxp : 0 < x := zero_lt_one.trans_le hx
  have hTp : 0 < T := zero_lt_one.trans_le hT
  have hleft : ‖VIntegral (removedIntegrand H x) (-1 / 16) (-T) T‖ ≤
      (102400 * B * x ^ (-1 / 16 : ℝ)) * Real.pi := by
    apply modFive_vertical_quadratic_bound hTp.le (by positivity)
    intro t ht
    have hs0 : (((-1 / 16 : ℝ) : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
      intro hs
      have := congrArg Complex.re hs
      norm_num at this
    have hp := removedIntegrand_point_bound χ hχ H hHd hExp hEuler
      (by norm_num : (-1 / 16 : ℝ) ≤ -1 / 16) (by norm_num)
      (abs_le.mpr ht) hs0 x
    apply hp.trans
    calc
      _ ≤ (400 * B) * (256 * x ^ (-1 / 16 : ℝ) / (1 + t ^ 2)) :=
        mul_le_mul_of_nonneg_left (left_kernel_bound hxp t) (by positivity)
      _ = _ := by ring
  have hrect : DifferentiableOn ℂ (removedIntegrand H x)
      (Rectangle (((-1 / 16 : ℝ) : ℂ) - Complex.I * (T : ℂ))
        ((2 : ℂ) + Complex.I * (T : ℂ))) := by
    apply (removedIntegrand_differentiableOn H hHd hxp).mono
    intro s hs
    have hs' : s.re ∈ Icc (-1 / 16 : ℝ) 2 ∧ s.im ∈ Icc (-T) T := by
      simpa [Rectangle, Complex.mem_reProdIm, uIcc_of_le (by norm_num : (-1 / 16 : ℝ) ≤ 2),
        uIcc_of_le (show -T ≤ T by linarith)] using hs
    have hre := hs'.1.1
    change (-1 / 8 : ℝ) < s.re
    linarith
  have hside (t : ℝ) (ht : |t| = T) : ∀ σ ∈ Icc (-1 / 16 : ℝ) 2,
      ‖removedIntegrand H x ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        400 * B * x ^ 2 / T ^ 2 := by
    intro σ hσ
    have ht0 : t ≠ 0 := by intro he; simp [he] at ht; linarith
    have hs0 : (σ : ℂ) + (t : ℂ) * Complex.I ≠ 0 := by
      intro he
      have hi := congrArg Complex.im he
      simp only [Complex.add_im, Complex.ofReal_im, Complex.ofReal_re, Complex.mul_im, Complex.I_re,
        Complex.I_im, zero_mul, mul_one, zero_add, add_zero, Complex.zero_im] at hi
      exact ht0 hi
    have hp := removedIntegrand_point_bound χ hχ H hHd hExp hEuler hσ.1 hσ.2 ht.le hs0 x
    have ht2 : t ^ 2 = T ^ 2 := by rw [← sq_abs, ht]
    apply hp.trans
    calc
      _ ≤ (400 * B) * (x ^ σ / t ^ 2) :=
        mul_le_mul_of_nonneg_left (modFive_perron_kernel_horizontal hxp σ ht0) (by positivity)
      _ ≤ (400 * B) * (x ^ (2 : ℝ) / T ^ 2) := by
        rw [ht2]
        gcongr
        exact hσ.2
      _ = _ := by rw [Real.rpow_two]; ring
  have hfin := modFive_rectangle_shift_bound (by norm_num : (-1 / 16 : ℝ) ≤ 2) hrect
    (hside T (abs_of_pos hTp)) (hside (-T) (by simp [abs_of_pos hTp]))
  have hπ := mul_le_mul_of_nonneg_left Real.pi_lt_four.le
    (by positivity : 0 ≤ 102400 * B * x ^ (-1 / 16 : ℝ))
  have hsum := hfin.trans (add_le_add (hleft.trans hπ) le_rfl)
  have ha : 0 ≤ B * x ^ (-1 / 16 : ℝ) := by positivity
  have hb : 0 ≤ B * (x ^ 2 / T ^ 2) := by positivity
  calc
    _ ≤ 409600 * (B * x ^ (-1 / 16 : ℝ)) + 1650 * (B * (x ^ 2 / T ^ 2)) :=
      hsum.trans_eq (by ring)
    _ ≤ 500000 * (B * x ^ (-1 / 16 : ℝ)) + 500000 * (B * (x ^ 2 / T ^ 2)) :=
      add_le_add (mul_le_mul_of_nonneg_right (by norm_num) ha)
        (mul_le_mul_of_nonneg_right (by norm_num) hb)
    _ = _ := by dsimp [B]; ring

#print axioms finite_contour_bound

end RealCharacterTail
