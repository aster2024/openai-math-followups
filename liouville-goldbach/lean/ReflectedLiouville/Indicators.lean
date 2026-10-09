import ReflectedLiouville.Algebra

set_option autoImplicit false
open scoped BigOperators

namespace ReflectedLiouville

lemma sign_indicator (z e : ℤ) (hz : IsSign z) (he : IsSign e) :
    (if z = e then (1 : ℝ) else 0) = (1 + (e : ℝ) * (z : ℝ)) / 2 := by
  rcases hz with rfl | rfl <;> rcases he with rfl | rfl <;> norm_num

lemma paired_sign_indicator (z₁ z₂ e₁ e₂ : ℤ)
    (hz₁ : IsSign z₁) (hz₂ : IsSign z₂) (he₁ : IsSign e₁) (he₂ : IsSign e₂) :
    (if z₁ = e₁ ∧ z₂ = e₂ then (1 : ℝ) else 0) =
      (1 + (e₁ : ℝ) * z₁ + (e₂ : ℝ) * z₂ +
        (e₁ : ℝ) * e₂ * z₁ * z₂) / 4 := by
  have hprod : (if z₁ = e₁ ∧ z₂ = e₂ then (1 : ℝ) else 0) =
      (if z₁ = e₁ then (1 : ℝ) else 0) * (if z₂ = e₂ then (1 : ℝ) else 0) := by
    split_ifs <;> simp_all
  rw [hprod, sign_indicator _ _ hz₁ he₁, sign_indicator _ _ hz₂ he₂]
  ring

lemma sign_pattern_count_identity (N : ℕ) (hN : 2 ≤ N) (e₁ e₂ : ℤ)
    (he₁ : IsSign e₁) (he₂ : IsSign e₂) :
    (signPatternCount N e₁ e₂ : ℝ) =
      ((N : ℝ) - 1 + ((e₁ : ℝ) + e₂) * linearSum N +
        (e₁ : ℝ) * e₂ * reflectedSum N) / 4 := by
  classical
  have hcount : (signPatternCount N e₁ e₂ : ℝ) =
      ∑ n ∈ reflectedIndices N,
        if ArithmeticFunction.liouville n = e₁ ∧ ArithmeticFunction.liouville (N - n) = e₂
        then (1 : ℝ) else 0 := by
    simp [signPatternCount]
  have hpoint (n : ℕ) (hn : n ∈ reflectedIndices N) :
      (if ArithmeticFunction.liouville n = e₁ ∧ ArithmeticFunction.liouville (N - n) = e₂
      then (1 : ℝ) else 0) =
        (1 + (e₁ : ℝ) * liouvilleReal n + (e₂ : ℝ) * liouvilleReal (N - n) +
          (e₁ : ℝ) * e₂ * (liouvilleReal n * liouvilleReal (N - n))) / 4 := by
    have hn' : 1 ≤ n ∧ n < N := Finset.mem_Ico.mp hn
    have hn0 : n ≠ 0 := by omega
    have hm0 : N - n ≠ 0 := by omega
    simpa only [liouvilleReal, mul_assoc] using
      paired_sign_indicator _ _ e₁ e₂ (liouville_int_isSign hn0)
        (liouville_int_isSign hm0) he₁ he₂
  rw [hcount]
  calc
    _ = ∑ n ∈ reflectedIndices N,
        (1 + (e₁ : ℝ) * liouvilleReal n + (e₂ : ℝ) * liouvilleReal (N - n) +
          (e₁ : ℝ) * e₂ * (liouvilleReal n * liouvilleReal (N - n))) / 4 :=
      Finset.sum_congr rfl hpoint
    _ = ((reflectedIndices N).card + (e₁ : ℝ) * linearSum N +
        (e₂ : ℝ) * linearSum N + (e₁ : ℝ) * e₂ * reflectedSum N) / 4 := by
      rw [← Finset.sum_div]
      simp only [Finset.sum_add_distrib, Finset.sum_const,
        nsmul_eq_mul, mul_one, ← Finset.mul_sum, linearSum_reflection,
        linearSum, reflectedSum]
    _ = _ := by
      rw [reflectedIndices_card]
      rw [Nat.cast_sub (by omega : 1 ≤ N)]
      norm_num
      ring

#print axioms sign_pattern_count_identity

end ReflectedLiouville
