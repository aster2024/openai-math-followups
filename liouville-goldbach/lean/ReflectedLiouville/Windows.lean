import ReflectedLiouville.Algebra

set_option autoImplicit false
open scoped BigOperators

namespace ReflectedLiouville

noncomputable def quotientWindow (z : ℕ → ℂ) (K h : ℕ) : ℂ :=
  (∑ v ∈ Finset.range K, ∑ j ∈ Finset.Icc 1 h, z (v + j)) / (h : ℂ)

lemma shifted_prefix_difference (z : ℕ → ℂ) (K j : ℕ) :
    (∑ v ∈ Finset.range K, z (v + j)) - (∑ v ∈ Finset.range K, z v) =
      (∑ v ∈ Finset.range j, z (K + v)) - (∑ v ∈ Finset.range j, z v) := by
  have h₁ := Finset.sum_range_add z K j
  have h₂ := Finset.sum_range_add z j K
  rw [Nat.add_comm j K] at h₂
  have hswap : (∑ v ∈ Finset.range K, z (j + v)) =
      ∑ v ∈ Finset.range K, z (v + j) := by
    apply Finset.sum_congr rfl
    intro v hv
    rw [Nat.add_comm]
  rw [hswap] at h₂
  linear_combination h₁ - h₂

lemma norm_prefix_le (z : ℕ → ℂ) (hz : ∀ k, ‖z k‖ ≤ 1) (K : ℕ) :
    ‖∑ k ∈ Finset.range K, z k‖ ≤ (K : ℝ) := by
  calc
    _ ≤ ∑ k ∈ Finset.range K, ‖z k‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.range K, (1 : ℝ) := Finset.sum_le_sum (fun k _ => hz k)
    _ = _ := by simp

lemma shifted_prefix_error (z : ℕ → ℂ) (hz : ∀ k, ‖z k‖ ≤ 1) (K j : ℕ) :
    ‖(∑ v ∈ Finset.range K, z (v + j)) - (∑ v ∈ Finset.range K, z v)‖ ≤ 2 * (j : ℝ) := by
  rw [shifted_prefix_difference]
  apply (norm_sub_le _ _).trans
  have htail := norm_prefix_le (fun v => z (K + v)) (fun v => hz (K + v)) j
  have hhead := norm_prefix_le z hz j
  linarith

lemma sum_Icc_one_natCast (h : ℕ) :
    (∑ j ∈ Finset.Icc 1 h, (j : ℝ)) = (h : ℝ) * (h + 1) / 2 := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ h + 1)]
    rw [ih]
    push_cast
    ring

/-- The deterministic averaged-window estimate, valid even when h exceeds K.
    It is the inequality actually needed by the paper's Fourier argument. -/
theorem quotient_window_error (z : ℕ → ℂ) (hz : ∀ k, ‖z k‖ ≤ 1) (K h : ℕ)
    (hh : 0 < h) :
    ‖quotientWindow z K h - (∑ k ∈ Finset.range K, z k)‖ ≤ (h : ℝ) + 1 := by
  have hhr : (0 : ℝ) < h := by exact_mod_cast hh
  have hhc : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  have hdiff : quotientWindow z K h - (∑ k ∈ Finset.range K, z k) =
      (∑ j ∈ Finset.Icc 1 h,
        ((∑ v ∈ Finset.range K, z (v + j)) - (∑ v ∈ Finset.range K, z v))) / (h : ℂ) := by
    unfold quotientWindow
    rw [Finset.sum_comm, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
    field_simp
  rw [hdiff, norm_div, Complex.norm_natCast]
  apply (div_le_iff₀ hhr).mpr
  calc
    _ ≤ ∑ j ∈ Finset.Icc 1 h,
        ‖(∑ v ∈ Finset.range K, z (v + j)) - (∑ v ∈ Finset.range K, z v)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.Icc 1 h, 2 * (j : ℝ) :=
      Finset.sum_le_sum (fun j _ => shifted_prefix_error z hz K j)
    _ = _ := by rw [← Finset.mul_sum, sum_Icc_one_natCast]; ring

/-- Literal l1 coefficient discrepancy; this is separate from the upper bound. -/
noncomputable def windowCoefficientL1 (K h : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (K + h),
    |((((Finset.range K) ×ˢ (Finset.Icc 1 h)).filter (fun vj => vj.1 + vj.2 = k)).card : ℝ) /
      h - (if k < K then (1 : ℝ) else 0)|

lemma coefficient_exactness_counterexample : windowCoefficientL1 1 2 = 2 := by
  have hI : Finset.Icc (1 : ℕ) 2 = {1, 2} := by decide
  norm_num [windowCoefficientL1, hI, Finset.sum_range_succ,
    Finset.filter_insert, Finset.filter_singleton]

#print axioms quotient_window_error
#print axioms coefficient_exactness_counterexample

end ReflectedLiouville
