import ReflectedLiouville.ExplicitBudget
import OAI.NumberTheory.TwoPoint.Circuits.CircuitDyadicComparison
import OAI.NumberTheory.TwoPoint.Circuits.CircuitLogarithmicBudget

set_option autoImplicit false
open OAI.TwoPointCorrelations
namespace ReflectedLiouville

/-- A derived finite-circuit property with its growth exponent exposed. -/
def BravermanFixed (K C : ℕ) : Prop :=
  ∀ (n : ℕ) (c : AC0Circuit n), c.depth ≤ 22 →
    ∀ ε : ℝ, 0 < ε → ε ≤ 1/2 → ∀ t : ℕ,
      (K : ℝ)*(Real.log ((c.size : ℝ)/ε))^C ≤ (t : ℝ) →
      ∀ g : BooleanCube n → ℝ, (∀ x, 0 ≤ g x) → cubeAverage g = 1 →
        TWiseUniformDensity g t →
        |cubeAverage (fun x => g x*c.indicator x)-cubeAverage c.indicator| ≤ ε

theorem explicit_logarithmic_degree_budget :
    ∃ K : ℕ, 0 < K ∧ ∀ m : ℕ, 1 ≤ m →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1/2 → ∀ t : ℕ,
        (K : ℝ)*(Real.log ((m : ℝ)/ε))^(8458 : ℕ) ≤ (t : ℝ) →
        ∃ j : ℕ, m ≤ 2^j ∧ (1/2 : ℝ)^j ≤ ε ∧ bravermanDegree j ≤ t := by
  obtain ⟨K,hK,hbound⟩ := braverman_degree_positive_explicit_exponent
  refine ⟨K*6^(8458 : ℕ),by positivity,?_⟩
  intro m hm ε hε hεhalf t ht
  obtain ⟨j,hmj,hjε,hjlog⟩ := dyadic_index_of_ratio m hm ε hε hεhalf
  refine ⟨j,hmj,hjε,?_⟩
  have hj : (bravermanDegree j : ℝ) ≤ (K : ℝ)*((j : ℝ)+1)^(8458 : ℕ) := by
    exact_mod_cast hbound j
  have hdeg : (bravermanDegree j : ℝ) ≤ (t : ℝ) := by
    calc
      _ ≤ _ := hj
      _ ≤ (K : ℝ)*(6*Real.log ((m : ℝ)/ε))^(8458 : ℕ) := by gcongr
      _ = ((K*6^(8458 : ℕ) : ℕ) : ℝ)*(Real.log ((m : ℝ)/ε))^(8458 : ℕ) := by
        push_cast
        rw [mul_pow]
        ring
      _ ≤ _ := ht
  exact_mod_cast hdeg

/-- The library's dyadic theorem yields the fixed exponent 8458 without
    extracting any opaque witness from `bravermanDepth22Input`. -/
theorem braverman_depth22_8458 : ∃ K : ℕ, 0 < K ∧ BravermanFixed K 8458 := by
  obtain ⟨K,hK,hbudget⟩ := explicit_logarithmic_degree_budget
  refine ⟨K,hK,?_⟩
  intro n c hc ε hε hεhalf t ht g hg hmean hwise
  obtain ⟨j,hmj,hεj,htj⟩ := hbudget c.size c.size_pos ε hε hεhalf t ht
  exact (c.dyadic_comparison hc hmj htj g hg hmean hwise).trans hεj

#print axioms braverman_depth22_8458
end ReflectedLiouville
