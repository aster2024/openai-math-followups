import ReflectedLiouville.Casts
import ReflectedLiouville.RealCutoff
import ReflectedLiouville.CenterExpansion

set_option autoImplicit false
open scoped BigOperators Classical
open OAI.TwoPointCorrelations

namespace ReflectedLiouville

lemma dilatedReflectedSum_cast (N a B : ℕ) :
    (dilatedReflectedSum N a B : ℂ) =
      ∑ x ∈ (Finset.Icc 1 B).filter (fun x => a ∣ x), liouville x * liouville (a * N - x) := by
  simp only [dilatedReflectedSum, Complex.ofReal_sum, Complex.ofReal_mul, liouvilleReal_cast]

lemma prefixReflectedSum_cast (N B : ℕ) :
    (prefixReflectedSum N B : ℂ) = ∑ x ∈ Finset.Icc 1 B, liouville x * liouville (N - x) := by
  simp only [prefixReflectedSum, Complex.ofReal_sum, Complex.ofReal_mul, liouvilleReal_cast]

/-- Exact complex dilation for the extracted nonraw mean-prime atom, retaining
    the real quotient cutoff Y=T/a. -/
theorem reflected_mean_atom_dilation (N a : ℕ) (ha : 0 < a) (T : ℝ) :
    (∑ x ∈ Finset.Icc 1 ⌊T⌋₊, natDivisibilityIndicator a x * liouville x * liouville (a * N - x)) =
      ∑ m ∈ Finset.Icc 1 ⌊T / a⌋₊, liouville m * liouville (N - m) := by
  have hfilter : (∑ x ∈ Finset.Icc 1 ⌊T⌋₊,
      natDivisibilityIndicator a x * liouville x * liouville (a * N - x)) =
      (dilatedReflectedSum N a ⌊T⌋₊ : ℂ) := by
    rw [dilatedReflectedSum_cast, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hd : a ∣ x <;> simp only [natDivisibilityIndicator, hd, ite_true, ite_false, one_mul, zero_mul]
  rw [hfilter, dilatedReflectedSum_eq_prefix N a ⌊T⌋₊ ha, prefixReflectedSum_cast,
    floor_div_natCast T a ha.ne']

#print axioms reflected_mean_atom_dilation

end ReflectedLiouville
