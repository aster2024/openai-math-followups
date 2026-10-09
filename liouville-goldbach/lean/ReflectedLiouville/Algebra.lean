import ReflectedLiouville.Definitions
import Mathlib.Tactic

set_option autoImplicit false
open scoped BigOperators

namespace ReflectedLiouville

lemma liouvilleReal_mul (m n : ℕ) :
    liouvilleReal (m * n) = liouvilleReal m * liouvilleReal n := by
  simp [liouvilleReal, ArithmeticFunction.liouville_apply_mul]

lemma liouvilleReal_sq {n : ℕ} (hn : n ≠ 0) : liouvilleReal n ^ 2 = 1 := by
  have h : (ArithmeticFunction.liouville n) ^ 2 = (1 : ℤ) := by
    rw [ArithmeticFunction.liouville_apply hn, ← pow_mul, Nat.mul_comm _ 2, pow_mul]
    norm_num
  unfold liouvilleReal
  exact_mod_cast h

lemma liouvilleReal_isSign {n : ℕ} (hn : n ≠ 0) :
    liouvilleReal n = -1 ∨ liouvilleReal n = 1 := by
  exact (sq_eq_one_iff.mp (liouvilleReal_sq hn)).symm

lemma liouville_int_isSign {n : ℕ} (hn : n ≠ 0) :
    IsSign (ArithmeticFunction.liouville n) := by
  rw [IsSign, ArithmeticFunction.liouville_apply hn]
  exact (neg_one_pow_eq_or ℤ _).symm

lemma abs_liouvilleReal {n : ℕ} (hn : n ≠ 0) : |liouvilleReal n| = 1 := by
  rcases liouvilleReal_isSign hn with h | h <;> simp [h]

lemma linearSum_reflection (N : ℕ) :
    (∑ n ∈ reflectedIndices N, liouvilleReal (N - n)) = linearSum N := by
  classical
  unfold linearSum reflectedIndices
  apply Finset.sum_bij (fun n _ => N - n)
  · intro n hn
    simp only [Finset.mem_Ico] at hn ⊢
    omega
  · intro a ha b hb hab
    simp only [Finset.mem_Ico] at ha hb
    omega
  · intro b hb
    refine ⟨N - b, ?_, ?_⟩
    · simp only [Finset.mem_Ico] at hb ⊢
      omega
    · simp only [Finset.mem_Ico] at hb
      omega
  · intro n hn
    rfl

lemma reflectedIndices_card (N : ℕ) : (reflectedIndices N).card = N - 1 := by
  simp [reflectedIndices]

/-- The exact complete-multiplicativity cancellation in the dilation proof. -/
lemma liouville_reflected_dilation (N a m : ℕ) (ha : a ≠ 0) :
    liouvilleReal (a * m) * liouvilleReal (a * N - a * m) =
      liouvilleReal m * liouvilleReal (N - m) := by
  rw [← Nat.mul_sub_left_distrib, liouvilleReal_mul, liouvilleReal_mul]
  have hs := liouvilleReal_sq ha
  calc
    _ = liouvilleReal a ^ 2 * (liouvilleReal m * liouvilleReal (N - m)) := by ring
    _ = _ := by rw [hs, one_mul]

lemma abs_liouvilleReal_le (n : ℕ) : |liouvilleReal n| ≤ 1 := by
  by_cases hn : n = 0
  · simp [hn, liouvilleReal]
  · exact (abs_liouvilleReal hn).le

lemma abs_reflected_term_le (N n : ℕ) :
    |liouvilleReal n * liouvilleReal (N - n)| ≤ 1 := by
  rw [abs_mul]
  exact (mul_le_mul (abs_liouvilleReal_le n) (abs_liouvilleReal_le (N - n))
    (abs_nonneg _) zero_le_one).trans_eq (by norm_num)

#print axioms liouville_reflected_dilation
#print axioms linearSum_reflection

end ReflectedLiouville
