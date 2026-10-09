import ReflectedLiouville.FiniteCauchy

set_option autoImplicit false
open scoped BigOperators

namespace ReflectedLiouville

def finitePrefix (z : ℕ → ℂ) (h : ℕ) : ℂ := ∑ j ∈ Finset.range h, z j

lemma finitePrefix_succ (z : ℕ → ℂ) (h : ℕ) : finitePrefix z (h + 1) = finitePrefix z h + z h := by
  simp only [finitePrefix, Finset.sum_range_succ]

/-- A finite exact Abel identity with no endpoint subtraction on naturals. -/
theorem finite_abel (z w : ℕ → ℂ) (h : ℕ) :
    (∑ j ∈ Finset.range h, z j * w j) =
      finitePrefix z h * w h +
        ∑ j ∈ Finset.range h, finitePrefix z (j + 1) * (w j - w (j + 1)) := by
  induction h with
  | zero => simp [finitePrefix]
  | succ h ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ, finitePrefix_succ]
    ring

/-- The norm form used to insert the small irrational frequency β. -/
theorem finite_abel_norm_bound (z w : ℕ → ℂ) (h : ℕ) (L : ℝ)
    (hw : ∀ j, ‖w j‖ ≤ 1) (hd : ∀ j, ‖w j - w (j + 1)‖ ≤ L) :
    ‖∑ j ∈ Finset.range h, z j * w j‖ ≤
      ‖finitePrefix z h‖ + L * (∑ j ∈ Finset.range h, ‖finitePrefix z (j + 1)‖) := by
  rw [finite_abel]
  apply (norm_add_le _ _).trans
  have hmain : ‖finitePrefix z h * w h‖ ≤ ‖finitePrefix z h‖ := by
    rw [norm_mul]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (hw h) (norm_nonneg _)
  have herror : ‖∑ j ∈ Finset.range h, finitePrefix z (j + 1) * (w j - w (j + 1))‖ ≤
      L * (∑ j ∈ Finset.range h, ‖finitePrefix z (j + 1)‖) := by
    apply (norm_sum_le _ _).trans
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    rw [norm_mul]
    have h := mul_le_mul_of_nonneg_left (hd j) (norm_nonneg (finitePrefix z (j + 1)))
    simpa only [mul_comm L] using h
  exact add_le_add hmain herror

#print axioms finite_abel_norm_bound

end ReflectedLiouville
