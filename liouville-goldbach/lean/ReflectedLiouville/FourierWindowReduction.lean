import ReflectedLiouville.WindowPerturbationMean
import ReflectedLiouville.Windows

set_option autoImplicit false
open scoped BigOperators

namespace ReflectedLiouville

lemma quotient_window_eq_frequency (N r K h : ℕ) (θ : ℝ) :
    quotientWindow (fun k => liouville (N * k + r) * OAI.TwoPointCorrelations.additiveCharacter θ k) K h =
      (∑ v ∈ Finset.range K, quotientWindowFrequency N r v h θ) / (h : ℂ) := by
  unfold quotientWindow quotientWindowFrequency
  congr 1
  apply Finset.sum_congr rfl
  intro v hv
  apply Finset.sum_bij (fun j _ => v + j)
  · intro j hj
    have := Finset.mem_Icc.mp hj
    exact Finset.mem_Icc.mpr (by omega)
  · intro j hj k hk heq
    omega
  · intro k hk
    have hk' := Finset.mem_Icc.mp hk
    refine ⟨k - v, Finset.mem_Icc.mpr (by omega), by omega⟩
  · intro j hj
    rfl

lemma quotient_prefix_window_norm (N r K h : ℕ) (θ : ℝ) (hh : 0 < h) :
    ‖∑ k ∈ Finset.range K, liouville (N * k + r) *
      OAI.TwoPointCorrelations.additiveCharacter θ k‖ ≤
      (∑ v ∈ Finset.range K, ‖quotientWindowFrequency N r v h θ‖) / (h : ℝ) + h + 1 := by
  let z := fun k => liouville (N * k + r) * OAI.TwoPointCorrelations.additiveCharacter θ k
  have hz : ∀ k, ‖z k‖ ≤ 1 := by
    intro k
    simp only [z, norm_mul, OAI.TwoPointCorrelations.norm_additiveCharacter, mul_one]
    exact norm_liouville_le _
  have he := quotient_window_error z hz K h hh
  have hnorm : ‖∑ k ∈ Finset.range K, z k‖ ≤ ‖quotientWindow z K h‖ + (h : ℝ) + 1 := by
    have ht := norm_sub_le (quotientWindow z K h) (quotientWindow z K h - ∑ k ∈ Finset.range K, z k)
    have hid : quotientWindow z K h - (quotientWindow z K h - ∑ k ∈ Finset.range K, z k) =
        ∑ k ∈ Finset.range K, z k := by ring
    rw [hid] at ht
    linarith
  dsimp only [z] at hnorm
  rw [quotient_window_eq_frequency, norm_div, Complex.norm_natCast] at hnorm
  have hdiv := div_le_div_of_nonneg_right
    (norm_sum_le (Finset.range K) (fun v => quotientWindowFrequency N r v h θ))
    (by positivity : (0 : ℝ) ≤ h)
  linarith

/-- Reduction to a single averaged window estimate, with the exact endpoint
    error carried through the residue average. -/
theorem quotient_fourier_of_window (N K h : ℕ) [NeZero N] [NeZero K]
    (θ A : ℝ) (hh : 0 < h) (hmean : quotientWindowMean N K h θ ≤ A * h) :
    (∑ r : Fin N, ‖∑ k ∈ Finset.range K, liouville (N * k + (r.val + 1)) *
      OAI.TwoPointCorrelations.additiveCharacter θ k‖) / (N : ℝ) ≤ A * K + h + 1 := by
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hK : (0 : ℝ) < K := by exact_mod_cast NeZero.pos K
  have hhr : (0 : ℝ) < h := by exact_mod_cast hh
  have hsum := Finset.sum_le_sum (fun r (_ : r ∈ (Finset.univ : Finset (Fin N))) =>
    quotient_prefix_window_norm N (r.val + 1) K h θ hh)
  have heq : (∑ r : Fin N, ((∑ v ∈ Finset.range K, ‖quotientWindowFrequency N (r.val + 1) v h θ‖) /
      (h : ℝ) + h + 1)) =
      (∑ v ∈ Finset.range K, ∑ r : Fin N, ‖quotientWindowFrequency N (r.val + 1) v h θ‖) /
        (h : ℝ) + (N : ℝ) * (h + 1) := by
    simp only [Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    rw [Finset.sum_comm]
    ring
  rw [heq] at hsum
  have hm : (∑ v ∈ Finset.range K, ∑ r : Fin N, ‖quotientWindowFrequency N (r.val + 1) v h θ‖) ≤
      A * (h : ℝ) * ((N : ℝ) * K) := by
    exact (div_le_iff₀ (mul_pos hN hK)).mp hmean
  have hmdiv := div_le_div_of_nonneg_right hm hhr.le
  have hsdiv := div_le_div_of_nonneg_right hsum hN.le
  have hid : A * (h : ℝ) * ((N : ℝ) * K) / h = A * (N : ℝ) * K := by field_simp <;> ring
  rw [hid] at hmdiv
  apply (div_le_iff₀ hN).mpr
  nlinarith

lemma sum_fin_shift_eq_Icc {α : Type*} [AddCommMonoid α] (N : ℕ) (f : ℕ → α) :
    (∑ r : Fin N, f (r.val + 1)) = ∑ r ∈ Finset.Icc 1 N, f r := by
  rw [Fin.sum_univ_eq_sum_range (fun r => f (r + 1))]
  apply Finset.sum_bij (fun r _ => r + 1)
  · intro r hr
    have := Finset.mem_range.mp hr
    exact Finset.mem_Icc.mpr (by omega)
  · intro r hr s hs heq
    omega
  · intro r hr
    have := Finset.mem_Icc.mp hr
    refine ⟨r - 1, Finset.mem_range.mpr (by omega), by omega⟩
  · intro r hr
    rfl

#print axioms quotient_fourier_of_window

end ReflectedLiouville
