import ReflectedLiouville.Main

set_option autoImplicit false
open scoped BigOperators

/-- Unfolded literal first-stage theorem, using Mathlib's integer Liouville
    function directly and the exact interval 1 ≤ n < N. -/
theorem reflected_liouville_log_saving_literal
    (h_KMT : ReflectedLiouville.KMTInput)
    (h_MRT : ReflectedLiouville.MRTRealTwistRepulsionInput) :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, 3 ≤ N₀ ∧
      ∀ N : ℕ, N₀ ≤ N →
        |∑ n ∈ Finset.Ico 1 N, (ArithmeticFunction.liouville n : ℝ) *
          (ArithmeticFunction.liouville (N-n) : ℝ)| ≤
            C*(N : ℝ)/Real.rpow (Real.log (N : ℝ)) c :=
  ReflectedLiouville.reflected_liouville_log_saving h_KMT h_MRT

#print reflected_liouville_log_saving_literal
#print ReflectedLiouville.reflected_liouville_main_and_sign_patterns
#print axioms ReflectedLiouville.reflected_liouville_log_saving
#print axioms ReflectedLiouville.reflected_liouville_sign_patterns
#print axioms ReflectedLiouville.reflected_liouville_main_and_sign_patterns
#print axioms reflected_liouville_log_saving_literal
