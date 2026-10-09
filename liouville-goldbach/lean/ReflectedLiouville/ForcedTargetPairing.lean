import ReflectedLiouville.FrameCoverage

set_option autoImplicit false
open scoped BigOperators Classical

namespace ReflectedLiouville

/-- Exact finite pairing for forced target sites. Cover is required only for
    nonzero coefficients, so ineligible long padding steps cause no demand. -/
theorem forced_target_pairing {V ι : Type*} [Fintype V]
    (site : V → ℤ) (hinj : Function.Injective site) (Q : Finset ι)
    (target : V → ι → ℤ) (C : V → ι → ℝ) (f : V → ℝ) (g : ℤ → ℝ)
    (hcover : ∀ i, ∀ q ∈ Q, f i * C i q ≠ 0 → ∃ j : V, site j = target i q) :
    (∑ i, ∑ j, f i * (∑ q ∈ Q, if site j = target i q then C i q else 0) * g (site j)) =
      ∑ i, ∑ q ∈ Q, f i * C i q * g (target i q) := by
  apply Finset.sum_congr rfl
  intro i hi
  have hrow : (∑ j : V, f i * (∑ q ∈ Q, if site j = target i q then C i q else 0) * g (site j)) =
      ∑ q ∈ Q, ∑ j : V, if site j = target i q then f i * C i q * g (site j) else 0 := by
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro q hq
    apply Finset.sum_congr rfl
    intro j hj
    split_ifs <;> ring
  rw [hrow]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hz : f i * C i q = 0
  · have hpoint (j : V) : (if site j = target i q then f i * C i q * g (site j) else 0) = 0 := by
      split_ifs <;> simp only [hz, zero_mul]
    simp only [hpoint, Finset.sum_const_zero, hz, zero_mul, ite_self]
  · obtain ⟨j₀, hj₀⟩ := hcover i q hq hz
    have heq (j : V) : site j = target i q ↔ j = j₀ := by
      exact ⟨fun h => hinj (h.trans hj₀.symm), fun h => h ▸ hj₀⟩
    simp only [heq, Finset.sum_ite_eq', Finset.mem_univ, ite_true, hj₀]

#print axioms forced_target_pairing

end ReflectedLiouville
