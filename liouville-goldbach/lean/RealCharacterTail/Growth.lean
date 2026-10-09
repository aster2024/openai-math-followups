import OAI.NumberTheory.DirichletL.Nonvanishing
import OAI.NumberTheory.SiegelZeros.Characters.SumCharacterPeriodZero
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Convex.Contractible

set_option autoImplicit false
open scoped BigOperators Topology
open Set Filter MeasureTheory

namespace RealCharacterTail

/-- The given zero-free input, specialized to nonprincipal characters. -/
theorem nonprincipal_nonzero {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {s : ℂ}
    (hs : (7 / 8 : ℝ) < s.re) : χ.LFunction s ≠ 0 :=
  OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re χ hs
    (fun h => hχ h.1)

/-- A modulus-uniform polynomial bound obtained from bounded character sums. -/
theorem norm_LFunction_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    ‖χ.LFunction s‖ ≤ ‖s‖ * (q : ℝ) / s.re := by
  have hint : IntegrableOn (fun t : ℝ => (q : ℝ) * t ^ (-s.re - 1)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : -s.re - 1 < -1)
      (by norm_num : (0 : ℝ) < 1)).const_mul (q : ℝ)
  have hI : ‖∫ t : ℝ in Ioi 1,
      (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, χ (k : ZMod q)) * (t : ℂ) ^ (-(s + 1))‖ ≤
      ∫ t : ℝ in Ioi 1, (q : ℝ) * t ^ (-s.re - 1) := by
    apply norm_integral_le_of_norm_le hint
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := zero_lt_one.trans ht
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    have he : (-(s + 1)).re = -s.re - 1 := by simp; ring
    rw [he]
    exact mul_le_mul_of_nonneg_right
      (OAI.SiegelZeros.WeightedTorusJets.norm_sum_character_Icc_lt χ hχ ⌊t⌋₊).le
      (Real.rpow_nonneg ht0.le _)
  have hvalue : (∫ t : ℝ in Ioi 1, (q : ℝ) * t ^ (-s.re - 1)) =
      (q : ℝ) / s.re := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt
      (by linarith : -s.re - 1 < -1) (by norm_num : (0 : ℝ) < 1)]
    simp
    ring
  rw [OAI.SiegelZeros.WeightedTorusJets.LFunction_eq_partial_sum_integral_of_re_pos
    χ hχ hs, norm_mul]
  simpa only [mul_div_assoc] using
    mul_le_mul_of_nonneg_left (hI.trans_eq hvalue) (norm_nonneg s)

/-- A fixed half-plane version convenient for logarithmic growth. -/
theorem norm_LFunction_le_two_mul {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {s : ℂ} (hs : (1 / 2 : ℝ) ≤ s.re) :
    ‖χ.LFunction s‖ ≤ 2 * (q : ℝ) * ‖s‖ := by
  have hp : 0 < s.re := by linarith
  apply (norm_LFunction_le χ hχ hp).trans
  apply (div_le_iff₀ hp).mpr
  nlinarith [mul_nonneg (Nat.cast_nonneg q) (norm_nonneg s)]

#print axioms nonprincipal_nonzero
#print axioms norm_LFunction_le
#print axioms norm_LFunction_le_two_mul

end RealCharacterTail
