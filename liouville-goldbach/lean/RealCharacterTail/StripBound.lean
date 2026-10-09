import RealCharacterTail.NormalizedLog

set_option autoImplicit false
open scoped Topology
open Set Filter

namespace RealCharacterTail

/-- Fixed-disc Borel--Caratheodory with all geometric constants explicit. -/
theorem norm_log_disc_le {H : ℂ → ℂ} {c z : ℂ} {M : ℝ}
    (hM : 1 ≤ M)
    (hH : DifferentiableOn ℂ H (Metric.ball c (17 / 8)))
    (hRe : ∀ w ∈ Metric.ball c (17 / 8), (H w).re ≤ M)
    (hcenter : ‖H c‖ ≤ 3 / 2) (hz : ‖z - c‖ ≤ 33 / 16) :
    ‖H z‖ ≤ 200 * M := by
  let F : ℂ → ℂ := fun w => H (c + w)
  have hmap : MapsTo (fun w : ℂ => c + w) (Metric.ball 0 (17 / 8))
      (Metric.ball c (17 / 8)) := by
    intro w hw
    simpa [Metric.mem_ball, dist_eq_norm] using hw
  have hFd : DifferentiableOn ℂ F (Metric.ball 0 (17 / 8)) :=
    hH.comp ((differentiable_const c).add differentiable_id).differentiableOn hmap
  have hFRe : MapsTo F (Metric.ball 0 (17 / 8)) {w | w.re ≤ M} :=
    fun w hw => hRe _ (hmap hw)
  have hzmem : z - c ∈ Metric.ball (0 : ℂ) (17 / 8) := by
    simp only [Metric.mem_ball, dist_zero_right]
    linarith
  have hb := Complex.borelCaratheodory (by linarith : 0 < M) hFd hFRe
    (by norm_num : (0 : ℝ) < 17 / 8) hzmem
  have hF0 : ‖F 0‖ ≤ 3 / 2 := by simpa [F] using hcenter
  have hd : 0 < 17 / 8 - ‖z - c‖ := by linarith
  have hdn : 1 / 16 ≤ 17 / 8 - ‖z - c‖ := by linarith
  have hnum : 0 ≤ 17 / 8 + ‖z - c‖ := by positivity
  have hfirst : 2 * M * ‖z - c‖ / (17 / 8 - ‖z - c‖) ≤ 66 * M := by
    apply (div_le_iff₀ hd).mpr
    have hm := mul_le_mul_of_nonneg_left hz (by linarith : 0 ≤ 68 * M)
    nlinarith
  have hsecond : ‖F 0‖ * (17 / 8 + ‖z - c‖) / (17 / 8 - ‖z - c‖) ≤ 201 / 2 := by
    calc
      _ ≤ (3 / 2) * (17 / 8 + ‖z - c‖) / (17 / 8 - ‖z - c‖) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hF0 hnum) hd.le
      _ ≤ 201 / 2 := by
        apply (div_le_iff₀ hd).mpr
        nlinarith
  have hresult := hb.trans (add_le_add hfirst hsecond)
  have heval : F (z - c) = H z := by dsimp [F]; congr 1; ring
  rw [heval] at hresult
  linarith

/-- Polynomial L-growth provides the real-part bound needed on the discs. -/
theorem log_re_bound_on_disc {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (H : ℂ → ℂ)
    (hExp : ∀ s : ℂ, (7 / 8 : ℝ) < s.re → Complex.exp (H s) = χ.LFunction s)
    (t : ℝ) {w : ℂ} (hw : w ∈ Metric.ball ((3 : ℂ) + (t : ℂ) * Complex.I) (17 / 8)) :
    (H w).re ≤ Real.log (20 * (q : ℝ) * (|t| + 2)) := by
  let c : ℂ := (3 : ℂ) + (t : ℂ) * Complex.I
  have hdist : ‖w - c‖ < 17 / 8 := by simpa [Metric.mem_ball, dist_eq_norm, c] using hw
  have hre : (7 / 8 : ℝ) < w.re := by
    have ha := (Complex.abs_re_le_norm (w - c)).trans_lt hdist
    simp [c] at ha
    have hl := (abs_lt.mp ha).1
    linarith
  have hnormc : ‖c‖ ≤ 3 + |t| := by
    simpa [c, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs] using
      norm_add_le (3 : ℂ) ((t : ℂ) * Complex.I)
  have hnormw : ‖w‖ ≤ |t| + 6 := by
    have ha := norm_le_norm_sub_add w c
    linarith
  have hgrowth := norm_LFunction_le_two_mul χ hχ (by linarith : (1 / 2 : ℝ) ≤ w.re)
  have hq0 : 0 ≤ (q : ℝ) := Nat.cast_nonneg q
  have hbound : ‖χ.LFunction w‖ ≤ 20 * (q : ℝ) * (|t| + 2) := by
    apply hgrowth.trans
    have hn := mul_le_mul_of_nonneg_left hnormw (by positivity : 0 ≤ 2 * (q : ℝ))
    have ht := mul_nonneg hq0 (abs_nonneg t)
    nlinarith
  have hlognorm : (H w).re = Real.log ‖χ.LFunction w‖ := by
    rw [← hExp w hre, Complex.norm_exp, Real.log_exp]
  rw [hlognorm]
  exact Real.log_le_log (norm_pos_iff.mpr (nonprincipal_nonzero χ hχ hre)) hbound

/-- Uniform logarithmic growth on the strip used by the Perron contour. -/
theorem normalized_log_strip_bound {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (H : ℂ → ℂ)
    (hHd : DifferentiableOn ℂ H {s | (7 / 8 : ℝ) < s.re})
    (hExp : ∀ s : ℂ, (7 / 8 : ℝ) < s.re → Complex.exp (H s) = χ.LFunction s)
    (hEuler : ∀ s : ℂ, 1 < s.re → H s = LSeries (logCoeff χ) s)
    {σ : ℝ} (hσ : 15 / 16 ≤ σ) (hσ3 : σ ≤ 3) (t : ℝ) :
    ‖H ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      200 * (Real.log (20 * (q : ℝ) * (|t| + 2)) + 1) := by
  let c : ℂ := (3 : ℂ) + (t : ℂ) * Complex.I
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hB : 1 ≤ 20 * (q : ℝ) * (|t| + 2) := by
    nlinarith [abs_nonneg t, mul_le_mul_of_nonneg_right hq1 (abs_nonneg t)]
  have hlog : 0 ≤ Real.log (20 * (q : ℝ) * (|t| + 2)) := Real.log_nonneg hB
  apply norm_log_disc_le (c := c) (by linarith)
  · apply hHd.mono
    intro w hw
    have hd : ‖w - c‖ < 17 / 8 := by simpa [Metric.mem_ball, dist_eq_norm] using hw
    have ha := (Complex.abs_re_le_norm (w - c)).trans_lt hd
    simp [c] at ha
    have hl := (abs_lt.mp ha).1
    change (7 / 8 : ℝ) < w.re
    linarith
  · intro w hw
    exact (log_re_bound_on_disc χ hχ H hExp t hw).trans (by linarith)
  · rw [hEuler c (by simp [c])]
    exact norm_logEuler_three_le χ t
  · have he : ((σ : ℂ) + (t : ℂ) * Complex.I) - c = ((σ - 3 : ℝ) : ℂ) := by
      dsimp [c]
      push_cast
      ring
    rw [he, Complex.norm_real, Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith, by linarith⟩

#print axioms norm_log_disc_le
#print axioms log_re_bound_on_disc
#print axioms normalized_log_strip_bound

end RealCharacterTail
