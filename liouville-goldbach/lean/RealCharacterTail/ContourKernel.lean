import RealCharacterTail.StripBound
import OAI.NumberTheory.TwoPoint.Fourier.ModFiveSmoothedContour

set_option autoImplicit false
open scoped Topology
open Set Filter MeasureTheory Complex Erdos970
open OAI.TwoPointCorrelations

namespace RealCharacterTail

/-- Subtract the value at one and fill the removable singularity at zero. -/
noncomputable def removedIntegrand (H : ℂ → ℂ) (x : ℝ) (s : ℂ) : ℂ :=
  dslope (fun w => H (1 + w)) 0 s * (x : ℂ) ^ s / (s + 1)

lemma removedIntegrand_eq (H : ℂ → ℂ) (x : ℝ) {s : ℂ} (hs : s ≠ 0) :
    removedIntegrand H x s = (H (1 + s) - H 1) * modFivePerronKernel x s := by
  rw [removedIntegrand, dslope_of_ne _ hs, slope_def_field]
  simp only [add_zero, sub_zero, modFivePerronKernel, div_eq_mul_inv, mul_inv_rev]
  ring

/-- The subtraction lets us shift through zero without a residue theorem. -/
theorem removedIntegrand_differentiableOn (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s | (7 / 8 : ℝ) < s.re}) {x : ℝ} (hx : 0 < x) :
    DifferentiableOn ℂ (removedIntegrand H x) {s | (-1 / 8 : ℝ) < s.re} := by
  let U : Set ℂ := {s | (-1 / 8 : ℝ) < s.re}
  have hUo : IsOpen U := Complex.continuous_re.isOpen_preimage _ isOpen_Ioi
  have h0 : (0 : ℂ) ∈ U := by norm_num [U]
  have htrans : DifferentiableOn ℂ (fun s => H (1 + s)) U := by
    apply hH.comp ((differentiable_const (1 : ℂ)).add differentiable_id).differentiableOn
    intro s hs
    change (-1 / 8 : ℝ) < s.re at hs
    change (7 / 8 : ℝ) < (1 + s).re
    simp only [Complex.add_re, Complex.one_re]
    linarith
  have hds : DifferentiableOn ℂ (dslope (fun s => H (1 + s)) 0) U :=
    (Complex.differentiableOn_dslope (hUo.mem_nhds h0)).mpr htrans
  have hp : DifferentiableOn ℂ (fun s : ℂ => (x : ℂ) ^ s) U := by
    intro s _
    exact (differentiableAt_id.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))).differentiableWithinAt
  apply (hds.mul hp).div ((differentiable_id.add (differentiable_const (1 : ℂ))).differentiableOn)
  intro s hs hz
  change s + 1 = 0 at hz
  have hr := congrArg Complex.re hz
  simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at hr
  change (-1 / 8 : ℝ) < s.re at hs
  linarith

/-- A quadratic denominator bound also valid on our negative left line. -/
lemma left_denominator (t : ℝ) :
    (1 + t ^ 2) / 256 ≤
      ‖(((-1 / 16 : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
        (((-1 / 16 : ℝ) : ℂ) + (t : ℂ) * Complex.I + 1)‖ := by
  let z : ℂ := ((-1 / 16 : ℝ) : ℂ) + (t : ℂ) * Complex.I
  have hnorm : ‖z‖ ≤ ‖z + 1‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [Complex.sq_norm, Complex.normSq_apply, z, Complex.add_re,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
      Complex.mul_im, Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im]
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hnorm (norm_nonneg z)
  rw [← sq, Complex.sq_norm] at hm
  have hz : Complex.normSq z = (1 / 256 : ℝ) + t ^ 2 := by
    simp [Complex.normSq_apply, z]
    ring
  rw [hz] at hm
  rw [norm_mul]
  change (1 + t ^ 2) / 256 ≤ ‖z‖ * ‖z + 1‖
  nlinarith [sq_nonneg t]

lemma left_kernel_bound {x : ℝ} (hx : 0 < x) (t : ℝ) :
    ‖modFivePerronKernel x (((-1 / 16 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      256 * x ^ (-1 / 16 : ℝ) / (1 + t ^ 2) := by
  rw [modFivePerronKernel, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_self, add_zero]
  exact (div_le_div_of_nonneg_left (Real.rpow_nonneg hx.le _)
    (by positivity : 0 < (1 + t ^ 2) / 256) (left_denominator t)).trans_eq (by field_simp)

/-- A finite-height form of the strip estimate. -/
lemma norm_log_height_bound {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (H : ℂ → ℂ)
    (hHd : DifferentiableOn ℂ H {s | (7 / 8 : ℝ) < s.re})
    (hExp : ∀ s : ℂ, (7 / 8 : ℝ) < s.re → Complex.exp (H s) = χ.LFunction s)
    (hEuler : ∀ s : ℂ, 1 < s.re → H s = LSeries (logCoeff χ) s)
    {σ t T : ℝ} (hσ : 15 / 16 ≤ σ) (hσ3 : σ ≤ 3) (ht : |t| ≤ T) :
    ‖H ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      200 * (Real.log (20 * (q : ℝ) * (T + 2)) + 1) := by
  apply (normalized_log_strip_bound χ hχ H hHd hExp hEuler hσ hσ3 t).trans
  have hq : 0 < (q : ℝ) := Nat.cast_pos.mpr (NeZero.pos q)
  have hb : 20 * (q : ℝ) * (|t| + 2) ≤ 20 * (q : ℝ) * (T + 2) := by gcongr
  have hl := Real.log_le_log (by positivity : 0 < 20 * (q : ℝ) * (|t| + 2)) hb
  linarith

#print axioms removedIntegrand_differentiableOn
#print axioms left_kernel_bound
#print axioms norm_log_height_bound

end RealCharacterTail
