import ReflectedLiouville.GcdSquareSums

set_option autoImplicit false
open MeasureTheory
open scoped BigOperators

namespace ReflectedLiouville

lemma unitResidueSquares_intervalIntegrable (d : ℕ) [NeZero d] (X H : ℝ)
    (hX : 0 ≤ X) (hH : 0 ≤ H) :
    IntervalIntegrable (fun x => unitResidueSquares d x H) volume X (2 * X) := by
  have h := unit_short_squares_intervalIntegrable d X H hX hH (fun _ => 0)
  simpa only [sub_zero, unitResidueSquares] using h

lemma scaled_unit_squares_intervalIntegrable (q : ℕ) [NeZero q] (u : ↥q.divisors) (X H : ℝ)
    (hX : 0 ≤ X) (hH : 0 ≤ H) :
    letI : NeZero (q / u.val) := ⟨quotient_divisor_ne_zero q u⟩
    IntervalIntegrable (fun x => unitResidueSquares (q / u.val) (x / u.val) (H / u.val)) volume X (2 * X) := by
  letI : NeZero (q / u.val) := ⟨quotient_divisor_ne_zero q u⟩
  have hup : (0 : ℝ) < u.val := by exact_mod_cast divisor_positive q u
  have h := unitResidueSquares_intervalIntegrable (q / u.val) (X / u.val) (H / u.val)
    (div_nonneg hX hup.le) (div_nonneg hH hup.le)
  have hcomp := h.comp_mul_right (c := (u.val : ℝ)⁻¹)
  convert hcomp using 1
  · funext x
    simp only [div_eq_mul_inv]
  · field_simp
  · field_simp

lemma unit_variance_scaling_integral (q : ℕ) [NeZero q] (u : ↥q.divisors) (X H : ℝ) :
    letI : NeZero (q / u.val) := ⟨quotient_divisor_ne_zero q u⟩
    (∫ x in X..2 * X, unitResidueSquares (q / u.val) (x / u.val) (H / u.val)) =
      (u.val : ℝ) * unitResidueVariance (q / u.val) (X / u.val) (H / u.val) := by
  letI : NeZero (q / u.val) := ⟨quotient_divisor_ne_zero q u⟩
  have hun : (u.val : ℝ) ≠ 0 := by exact_mod_cast (divisor_positive q u).ne'
  have hi := intervalIntegral.integral_comp_div
    (a := X) (b := 2 * X) (fun y : ℝ => unitResidueSquares (q / u.val) y (H / u.val)) hun
  rw [smul_eq_mul] at hi
  calc
    _ = (u.val : ℝ) * (∫ y in X / u.val..(2 * X) / u.val,
        unitResidueSquares (q / u.val) y (H / u.val)) := hi
    _ = _ := by
      unfold unitResidueVariance unitResidueSquares
      congr 1
      congr 1
      ring

/-- Exact integral decomposition. Every integrability premise is supplied by
    the concrete finite short-sum proof before exchanging the sum and integral. -/
theorem allResidueVariance_gcd (q : ℕ) [NeZero q] (X H : ℝ) (hX : 0 ≤ X) (hH : 0 ≤ H) :
    allResidueVariance q X H =
      ∑ u : ↥q.divisors,
        letI : NeZero (q / u.val) := ⟨quotient_divisor_ne_zero q u⟩
        (u.val : ℝ) * unitResidueVariance (q / u.val) (X / u.val) (H / u.val) := by
  have hpoint : (fun x => ∑ a : ZMod q, ‖shortProgressionSum liouville q a x H‖ ^ (2 : ℕ)) =
      (fun x => ∑ u : ↥q.divisors,
        letI : NeZero (q / u.val) := ⟨quotient_divisor_ne_zero q u⟩
        unitResidueSquares (q / u.val) (x / u.val) (H / u.val)) := by
    funext x
    exact all_residue_squares_gcd q x H hH
  unfold allResidueVariance
  rw [hpoint]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro u hu
    exact unit_variance_scaling_integral q u X H
  · intro u hu
    exact scaled_unit_squares_intervalIntegrable q u X H hX hH

#print axioms allResidueVariance_gcd

end ReflectedLiouville
