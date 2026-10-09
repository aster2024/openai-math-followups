import ReflectedLiouville.Algebra

set_option autoImplicit false
open scoped BigOperators

namespace ReflectedLiouville

lemma liouvilleReal_cast (n : ℕ) : (liouvilleReal n : ℂ) = liouville n := by
  simp [liouvilleReal, OAI.TwoPointCorrelations.liouville]

lemma reflectedSum_cast (N : ℕ) :
    (reflectedSum N : ℂ) =
      ∑ n ∈ reflectedIndices N, liouville n * liouville (N - n) := by
  simp [reflectedSum, liouvilleReal_cast]

lemma linearSum_cast (N : ℕ) :
    (linearSum N : ℂ) = ∑ n ∈ reflectedIndices N, liouville n := by
  simp [linearSum, liouvilleReal_cast]

lemma norm_reflectedComplexSum (N : ℕ) :
    ‖∑ n ∈ reflectedIndices N, liouville n * liouville (N - n)‖ = |reflectedSum N| := by
  rw [← reflectedSum_cast, Complex.norm_real, Real.norm_eq_abs]

lemma norm_liouville_le (n : ℕ) : ‖liouville n‖ ≤ 1 := by
  rw [← liouvilleReal_cast, Complex.norm_real, Real.norm_eq_abs]
  exact abs_liouvilleReal_le n

#print axioms reflectedSum_cast

end ReflectedLiouville
