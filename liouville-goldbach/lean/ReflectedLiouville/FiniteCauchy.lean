import ReflectedLiouville.Algebra

set_option autoImplicit false
open scoped BigOperators

namespace ReflectedLiouville

lemma finite_real_cauchy {ι : Type*} (S : Finset ι) (f : ι → ℝ) :
    (∑ i ∈ S, f i) ^ 2 ≤ (S.card : ℝ) * (∑ i ∈ S, (f i) ^ 2) := by
  have hnonneg : 0 ≤ ∑ i ∈ S, ∑ j ∈ S, (f i - f j) ^ 2 := by
    exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))
  have hid : (∑ i ∈ S, ∑ j ∈ S, (f i - f j) ^ 2) =
      2 * (S.card : ℝ) * (∑ i ∈ S, (f i) ^ 2) - 2 * (∑ i ∈ S, f i) ^ 2 := by
    simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum, ← Finset.sum_mul]
    ring
  rw [hid] at hnonneg
  linarith

lemma finite_complex_cauchy {ι : Type*} (S : Finset ι) (f : ι → ℂ) :
    ‖∑ i ∈ S, f i‖ ^ 2 ≤ (S.card : ℝ) * (∑ i ∈ S, ‖f i‖ ^ 2) := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le S f) 2
  exact h.trans (finite_real_cauchy S (fun i => ‖f i‖))

lemma finite_mean_norm_le_sqrt_mean_square {ι : Type*} (S : Finset ι) (f : ι → ℂ)
    (hS : 0 < S.card) :
    (∑ i ∈ S, ‖f i‖) / (S.card : ℝ) ≤
      Real.sqrt ((∑ i ∈ S, ‖f i‖ ^ 2) / (S.card : ℝ)) := by
  have hcard : (0 : ℝ) < S.card := by exact_mod_cast hS
  have hsum : 0 ≤ ∑ i ∈ S, ‖f i‖ := Finset.sum_nonneg (fun i _ => norm_nonneg _)
  have hsum₂ : 0 ≤ ∑ i ∈ S, ‖f i‖ ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hCauchy := finite_real_cauchy S (fun i => ‖f i‖)
  have hsq : ((∑ i ∈ S, ‖f i‖) / (S.card : ℝ)) ^ 2 ≤
      (∑ i ∈ S, ‖f i‖ ^ 2) / (S.card : ℝ) := by
    rw [div_pow]
    apply (div_le_div_iff₀ (pow_pos hcard 2) hcard).mpr
    nlinarith
  exact Real.le_sqrt_of_sq_le hsq

#print axioms finite_complex_cauchy

end ReflectedLiouville
