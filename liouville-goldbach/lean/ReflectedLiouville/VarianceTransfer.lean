import ReflectedLiouville.MainTermEnergy
import Mathlib.Tactic

set_option autoImplicit false
open MeasureTheory
open scoped BigOperators

namespace ReflectedLiouville

lemma norm_square_uncenter (z w : ℂ) : ‖z‖ ^ 2 ≤ 2 * ‖z - w‖ ^ 2 + 2 * ‖w‖ ^ 2 := by
  have hsum : ‖z‖ ≤ ‖z - w‖ + ‖w‖ := by
    simpa only [sub_add_cancel] using norm_add_le (z - w) w
  nlinarith [norm_nonneg z, norm_nonneg (z - w), norm_nonneg w,
    sq_nonneg (‖z - w‖ - ‖w‖)]

lemma square_sum_uncenter {ι : Type*} [Fintype ι] (z w : ι → ℂ) :
    (∑ a, ‖z a‖ ^ 2) ≤ 2 * (∑ a, ‖z a - w a‖ ^ 2) + 2 * (∑ a, ‖w a‖ ^ 2) := by
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun a _ => norm_square_uncenter (z a) (w a))

/-- Integrability is explicit in this deterministic lemma; applying it to
    short-progression sums requires proving those concrete integrability facts. -/
lemma integrated_square_sum_uncenter {ι : Type*} [Fintype ι]
    (z : ℝ → ι → ℂ) (w : ι → ℂ) (X : ℝ) (hX : 0 ≤ X)
    (hz : IntervalIntegrable (fun x => ∑ a, ‖z x a‖ ^ 2) volume X (2 * X))
    (hc : IntervalIntegrable (fun x => ∑ a, ‖z x a - w a‖ ^ 2) volume X (2 * X)) :
    (∫ x in X..2 * X, ∑ a, ‖z x a‖ ^ 2) ≤
      2 * (∫ x in X..2 * X, ∑ a, ‖z x a - w a‖ ^ 2) +
        2 * X * (∑ a, ‖w a‖ ^ 2) := by
  have hconstant : IntervalIntegrable (fun _x : ℝ => 2 * (∑ a, ‖w a‖ ^ 2)) volume X (2 * X) :=
    intervalIntegrable_const
  have hright : IntervalIntegrable
      (fun x => 2 * (∑ a, ‖z x a - w a‖ ^ 2) + 2 * (∑ a, ‖w a‖ ^ 2)) volume X (2 * X) :=
    (hc.const_mul 2).add hconstant
  have hbound := intervalIntegral.integral_mono_on (by linarith : X ≤ 2 * X) hz hright
    (fun x _ => square_sum_uncenter (z x) w)
  rw [intervalIntegral.integral_add (hc.const_mul 2) hconstant,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul] at hbound
  convert hbound using 1 <;> ring

#print axioms integrated_square_sum_uncenter

end ReflectedLiouville
