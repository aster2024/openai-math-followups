import ReflectedLiouville.OriginCellIntegral

set_option autoImplicit false
open MeasureTheory
open scoped BigOperators

namespace ReflectedLiouville

lemma origin_cell_integrals_sum (Q N K : ℕ) [NeZero Q] (H : ℝ) (hH : 0 ≤ H) :
    (∑ v ∈ Finset.range K,
      ∫ x in ((N * v : ℕ) : ℝ)..(((N * v : ℕ) : ℝ) + N), allResidueSquares Q x H) =
      ∫ x in (0 : ℝ)..((N * K : ℕ) : ℝ), allResidueSquares Q x H := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ih]
    have hInt₁ := allResidueSquares_intervalIntegrable_on Q 0 ((N * K : ℕ) : ℝ) H (by positivity) hH
    have hInt₂ := allResidueSquares_intervalIntegrable_on Q ((N * K : ℕ) : ℝ)
      (((N * K : ℕ) : ℝ) + N) H (by have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N; linarith) hH
    rw [intervalIntegral.integral_add_adjacent_intervals hInt₁ hInt₂]
    congr 1
    push_cast
    ring

/-- Explicit version of paper equation startaverage. No frequency supremum is
    moved through an average or integral. -/
theorem rational_windows_discrete_to_integral (N q₀ K h : ℕ) [NeZero N] [NeZero q₀] (a : ℤ) :
    (∑ v ∈ Finset.range K, ∑ r : Fin N,
      ‖rationalQuotientWindow N q₀ (r.val + 1) v h a‖ ^ (2 : ℕ)) ≤
      (2 * (q₀ : ℝ) / N) *
        (∫ x in (0 : ℝ)..((N * K : ℕ) : ℝ), allResidueSquares (N * q₀) x ((N * h : ℕ) : ℝ)) +
        8 * (N : ℝ) * K * (q₀ : ℝ) ^ (2 : ℕ) := by
  have hsum := Finset.sum_le_sum (fun v (_hv : v ∈ Finset.range K) => rational_window_origin_cell N q₀ v h a)
  calc
    _ ≤ ∑ v ∈ Finset.range K,
        ((2 * (q₀ : ℝ) / N) *
          (∫ x in ((N * v : ℕ) : ℝ)..(((N * v : ℕ) : ℝ) + N),
            allResidueSquares (N * q₀) x ((N * h : ℕ) : ℝ)) +
          8 * (N : ℝ) * (q₀ : ℝ) ^ (2 : ℕ)) := hsum
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, origin_cell_integrals_sum _ _ _ _ (Nat.cast_nonneg _)]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring

#print axioms rational_windows_discrete_to_integral

end ReflectedLiouville
