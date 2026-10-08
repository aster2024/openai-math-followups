import OAI.NumberTheory.TwoPointCorrelations.FinalMain

set_option autoImplicit false
open OAI.TwoPointCorrelations
open scoped BigOperators

namespace ReflectedLiouville

variable {ι : Type*} [Fintype ι]

noncomputable def bipartiteKernel (A : ι → ι → ℂ) : (Bool × ι) → (Bool × ι) → ℂ
  | (false, i), (true, j) => A i j
  | (true, i), (false, j) => star (A j i)
  | _, _ => 0

lemma bipartite_norm_symm (A : ι → ι → ℂ) (i j : Bool × ι) :
    ‖bipartiteKernel A i j‖ = ‖bipartiteKernel A j i‖ := by
  rcases i with ⟨b, i⟩; rcases j with ⟨c, j⟩
  cases b <;> cases c <;> simp [bipartiteKernel]

lemma bipartite_level (A : ι → ι → ℂ) (a : ι → ℝ)
    (hlevel : ∀ i j, A i j ≠ 0 → a i = a j)
    (i j : Bool × ι) (hn : bipartiteKernel A i j ≠ 0) : a i.2 = a j.2 := by
  rcases i with ⟨b, i⟩; rcases j with ⟨c, j⟩
  cases b <;> cases c <;> simp [bipartiteKernel] at hn ⊢
  · exact hlevel i j hn
  · exact (hlevel j i hn).symm

lemma bipartite_weighted_row (A : ι → ι → ℂ) (g a : ι → ℝ) (K : ℝ)
    (hleft : ∀ i, ∑ j, ‖A i j‖ * g j / g i ≤ K * a i)
    (hright : ∀ i, ∑ j, ‖A j i‖ * g j / g i ≤ K * a i)
    (i : Bool × ι) :
    ∑ j : Bool × ι, ‖bipartiteKernel A i j‖ * g j.2 / g i.2 ≤ K * a i.2 := by
  rcases i with ⟨b, i⟩
  cases b
  · simpa [Fintype.sum_prod_type, bipartiteKernel] using hleft i
  · simpa [Fintype.sum_prod_type, bipartiteKernel] using hright i

/-- The duplicated site projection has no injectivity hypothesis. -/
theorem two_layer_localized_square (A : ι → ι → ℂ) (g a : ι → ℝ) (K : ℝ)
    (hK : 0 ≤ K) (hg : ∀ i, 0 < g i) (ha : ∀ i, 0 ≤ a i)
    (hlevel : ∀ i j, A i j ≠ 0 → a i = a j)
    (hleft : ∀ i, ∑ j, ‖A i j‖ * g j / g i ≤ K * a i)
    (hright : ∀ i, ∑ j, ‖A j i‖ * g j / g i ≤ K * a i)
    (v : (Bool × ι) → ℂ) :
    ∑ i : Bool × ι, ‖∑ j : Bool × ι, bipartiteKernel A i j * v j‖ ^ 2 ≤
      K ^ 2 * ∑ i : Bool × ι, (a i.2) ^ 2 * ‖v i‖ ^ 2 := by
  exact weighted_matrix_localized_square (bipartiteKernel A)
    (fun i => g i.2) (fun i => a i.2) K hK
    (fun i => hg i.2) (fun i => ha i.2)
    (bipartite_norm_symm A) (bipartite_level A a hlevel)
    (bipartite_weighted_row A g a K hleft hright) v

#print axioms ReflectedLiouville.two_layer_localized_square
end ReflectedLiouville
