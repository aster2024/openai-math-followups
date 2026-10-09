import RealCharacterTail.Logarithm
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries

set_option autoImplicit false
open scoped BigOperators Topology ComplexOrder
open Set Filter MeasureTheory

namespace RealCharacterTail

/-- Coefficients of the logarithm of the Euler product. -/
noncomputable def logCoeff {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  χ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ) / (Real.log (n : ℝ) : ℂ)

@[simp] theorem logCoeff_zero {q : ℕ} (χ : DirichletCharacter ℂ q) : logCoeff χ 0 = 0 := by
  simp [logCoeff]

@[simp] theorem logCoeff_one {q : ℕ} (χ : DirichletCharacter ℂ q) : logCoeff χ 1 = 0 := by
  simp [logCoeff]

/-- The logarithmic Euler coefficients are absolutely bounded by one. -/
theorem norm_logCoeff_le_one {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) :
    ‖logCoeff χ n‖ ≤ 1 := by
  by_cases hn : 1 < n
  · have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
    rw [logCoeff, norm_div, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := n)), abs_of_pos hlog]
    apply (div_le_one hlog).mpr
    exact (mul_le_of_le_one_left (ArithmeticFunction.vonMangoldt_nonneg (n := n))
      (χ.norm_le_one (n : ZMod q))).trans ArithmeticFunction.vonMangoldt_le_log
  · have hn' : n = 0 ∨ n = 1 := by omega
    rcases hn' with rfl | rfl <;> simp

/-- Absolute convergence on the classical Euler-product half-plane. -/
theorem logCoeff_summable {q : ℕ} (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 1 < s.re) : LSeriesSummable (logCoeff χ) s :=
  LSeriesSummable_of_bounded_of_one_lt_re (fun n _ => norm_logCoeff_le_one χ n) hs

theorem logCoeff_abscissa_le_one {q : ℕ} (χ : DirichletCharacter ℂ q) :
    LSeries.abscissaOfAbsConv (logCoeff χ) ≤ 1 :=
  LSeries.abscissaOfAbsConv_le_of_le_const ⟨1, fun n _ => norm_logCoeff_le_one χ n⟩

theorem logEuler_differentiableAt {q : ℕ} (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 1 < s.re) : DifferentiableAt ℂ (LSeries (logCoeff χ)) s := by
  apply (LSeries_hasDerivAt _).differentiableAt
  exact lt_of_le_of_lt (logCoeff_abscissa_le_one χ) (by exact_mod_cast hs)

/-- The exponential of the Euler logarithm is the actual Dirichlet L-function. -/
theorem exp_logEuler {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 1 < s.re) : Complex.exp (LSeries (logCoeff χ) s) = χ.LFunction s := by
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
  exact χ.LSeries_eq_exp_LSeries hs

/-- A uniform bound at a vertical line strictly within absolute convergence. -/
theorem norm_logEuler_three_le {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) :
    ‖LSeries (logCoeff χ) ((3 : ℂ) + (t : ℂ) * Complex.I)‖ ≤ 3 / 2 := by
  let s : ℂ := (3 : ℂ) + (t : ℂ) * Complex.I
  have hs : 1 < s.re := by simp [s]
  have hsum := logCoeff_summable χ hs
  have hone : LSeriesSummable (fun _ : ℕ => (1 : ℂ)) (3 : ℂ) :=
    LSeriesSummable_of_bounded_of_one_lt_re (fun _ _ => le_rfl) (by norm_num)
  calc
    ‖LSeries (logCoeff χ) s‖ ≤ ∑' n, ‖LSeries.term (logCoeff χ) s n‖ :=
      norm_tsum_le_tsum_norm hsum.norm
    _ ≤ ∑' n, ‖LSeries.term (fun _ : ℕ => (1 : ℂ)) (3 : ℂ) n‖ := by
      apply hsum.norm.tsum_le_tsum _ hone.norm
      intro n
      have hb := LSeries.norm_term_le (g := fun _ : ℕ => (1 : ℂ)) s
        (by simpa using norm_logCoeff_le_one χ n)
      simpa only [LSeries.norm_term_eq, s, Complex.add_re, Complex.ofReal_re,
        Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        mul_zero, zero_mul, sub_self, add_zero] using hb
    _ = (riemannZeta (3 : ℂ)).re := by
      rw [← ArithmeticFunction.LSeries_zeta_eq_riemannZeta (by norm_num),
        ArithmeticFunction.LSeries_zeta_eq]
      change (∑' n, ‖LSeries.term (fun _ : ℕ => (1 : ℂ)) (3 : ℂ) n‖) =
        (LSeries (fun _ : ℕ => (1 : ℂ)) (3 : ℂ)).re
      rw [LSeries, Complex.re_tsum hone]
      apply tsum_congr
      intro n
      have hnonneg : 0 ≤ LSeries.term (fun _ : ℕ => (1 : ℂ)) (3 : ℂ) n :=
        LSeries.term_nonneg (by norm_num) 3
      simpa using congrArg Complex.re (RCLike.norm_of_nonneg' hnonneg)
    _ ≤ 3 / 2 := by
      have hb := OAI.SiegelZeros.WeightedTorusJets.riemannZeta_re_le_one_add_inv
        (by norm_num : (1 : ℝ) < 3)
      norm_num at hb ⊢
      exact hb

#print axioms norm_logCoeff_le_one
#print axioms logCoeff_summable
#print axioms exp_logEuler
#print axioms norm_logEuler_three_le

end RealCharacterTail
