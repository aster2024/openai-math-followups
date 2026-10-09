import ReflectedLiouville.ExplicitMain
import ReflectedLiouville.ExplicitComparisonCatalogue

set_option autoImplicit false
open scoped BigOperators Classical

theorem paper_theorem_1_1_explicit_literal
    (h_KMT : ReflectedLiouville.KMTInput)
    (h_MRT : ReflectedLiouville.MRTRealTwistRepulsionInput) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      (|∑ n ∈ Finset.Ico 1 N, (ArithmeticFunction.liouville n : ℝ) *
          (ArithmeticFunction.liouville (N-n) : ℝ)| ≤
        C*(N : ℝ)/Real.rpow (Real.log (N : ℝ)) (1/(10 : ℝ)^(200 : ℕ))) ∧
      (∀ e₁ e₂ : ℤ, (e₁ = -1 ∨ e₁ = 1) → (e₂ = -1 ∨ e₂ = 1) →
        |((((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)).filter (fun ab =>
            ab.1+ab.2 = N ∧ ArithmeticFunction.liouville ab.1 = e₁ ∧
              ArithmeticFunction.liouville ab.2 = e₂)).card : ℝ) - (N : ℝ)/4| ≤
          C*(N : ℝ)/Real.rpow (Real.log (N : ℝ)) (1/(10 : ℝ)^(200 : ℕ))) :=
  ReflectedLiouville.paper_theorem_1_1_explicit h_KMT h_MRT

#print paper_theorem_1_1_explicit_literal
#print axioms ReflectedLiouville.paper_theorem_1_1_explicit
#print axioms paper_theorem_1_1_explicit_literal
#print axioms ReflectedLiouville.binned_reflected_saving_with_bounded_A
#print axioms ReflectedLiouville.paper_star_exponent_value
