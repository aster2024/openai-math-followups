import ReflectedLiouville.WindowIntegrability

set_option autoImplicit false
open MeasureTheory
open scoped BigOperators

namespace ReflectedLiouville

/-- Average each quotient-origin cell using the actual measurable short sums.
    Constants match the preceding pointwise q₀-Cauchy and endpoint bounds. -/
theorem rational_window_origin_cell (N q₀ v h : ℕ) [NeZero N] [NeZero q₀] (a : ℤ) :
    (∑ r : Fin N, ‖rationalQuotientWindow N q₀ (r.val + 1) v h a‖ ^ (2 : ℕ)) ≤
      (2 * (q₀ : ℝ) / N) *
        (∫ x in ((N * v : ℕ) : ℝ)..(((N * v : ℕ) : ℝ) + N),
          allResidueSquares (N * q₀) x ((N * h : ℕ) : ℝ)) +
        8 * (N : ℝ) * (q₀ : ℝ) ^ (2 : ℕ) := by
  let E := ∑ r : Fin N, ‖rationalQuotientWindow N q₀ (r.val + 1) v h a‖ ^ (2 : ℕ)
  let F := fun s : ℝ => allResidueSquares (N * q₀) (((N * v : ℕ) : ℝ) + s) ((N * h : ℕ) : ℝ)
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hF : IntervalIntegrable F volume 0 N :=
    allResidueSquares_translated_intervalIntegrable _ _ _ _ hN.le (Nat.cast_nonneg _)
  have hconst : IntervalIntegrable (fun _s : ℝ => (8 : ℝ) * N * (q₀ : ℝ) ^ (2 : ℕ)) volume 0 N :=
    intervalIntegrable_const
  have hright : IntervalIntegrable (fun s => 2 * (q₀ : ℝ) * F s + 8 * (N : ℝ) * (q₀ : ℝ) ^ (2 : ℕ)) volume 0 N :=
    (hF.const_mul _).add hconst
  have hleft : IntervalIntegrable (fun _s : ℝ => E) volume 0 N := intervalIntegrable_const
  have hbound := intervalIntegral.integral_mono_on hN.le hleft hright (fun s hs =>
    rational_window_shared_origin N q₀ v h a s hs.1 hs.2)
  rw [intervalIntegral.integral_const, intervalIntegral.integral_add (hF.const_mul _) hconst,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul, smul_eq_mul,
    sub_zero] at hbound
  have htranslate := intervalIntegral.integral_comp_add_left (a := (0 : ℝ)) (b := (N : ℝ))
    (fun x => allResidueSquares (N * q₀) x ((N * h : ℕ) : ℝ)) ((N * v : ℕ) : ℝ)
  simp only [add_zero] at htranslate
  change (∫ s in (0 : ℝ)..(N : ℝ), F s) = _ at htranslate
  rw [htranslate] at hbound
  apply (mul_le_mul_iff_left₀ hN).mp
  have hid :
      ((2 * (q₀ : ℝ) / N) *
        (∫ x in ((N * v : ℕ) : ℝ)..(((N * v : ℕ) : ℝ) + N),
          allResidueSquares (N * q₀) x ((N * h : ℕ) : ℝ)) +
        8 * (N : ℝ) * (q₀ : ℝ) ^ (2 : ℕ)) * N =
      2 * (q₀ : ℝ) *
        (∫ x in ((N * v : ℕ) : ℝ)..(((N * v : ℕ) : ℝ) + N),
          allResidueSquares (N * q₀) x ((N * h : ℕ) : ℝ)) +
        (N : ℝ) * (8 * (N : ℝ) * (q₀ : ℝ) ^ (2 : ℕ)) := by field_simp <;> ring
  rw [hid]
  simpa only [E, mul_comm (N : ℝ)] using hbound

#print axioms rational_window_origin_cell

end ReflectedLiouville
