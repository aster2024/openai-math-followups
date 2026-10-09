import ReflectedLiouville.Algebra
import OAI.NumberTheory.TwoPoint.Bounds.PrimePhysicalMatrix

set_option autoImplicit false
open scoped BigOperators Classical
open OAI.TwoPointCorrelations

namespace ReflectedLiouville

noncomputable def liouvilleAtInteger (x : ℤ) : ℝ := liouvilleReal x.toNat

lemma liouvilleAtInteger_of_nonpos (x : ℤ) (hx : x ≤ 0) : liouvilleAtInteger x = 0 := by
  simp [liouvilleAtInteger, Int.toNat_of_nonpos hx, liouvilleReal]

lemma abs_liouvilleAtInteger_le (x : ℤ) : |liouvilleAtInteger x| ≤ 1 := abs_liouvilleReal_le _

lemma increasing_edge_zero_below (Q : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → Prop)
    (g center : ℤ → ℝ) (L K : ℝ) (extra : ℤ → Prop) (h d q : ℕ)
    (n m : ℤ) (hmn : m < n) : directedIntegerEdge Q u eligible g center L K extra h d q n m = 0 := by
  unfold directedIntegerEdge
  have hnot : ¬m = n + ((h * q * d : ℕ) : ℤ) := by
    have hp : (0 : ℤ) ≤ (h * q * d : ℕ) := Int.natCast_nonneg _
    omega
  simp only [hnot, and_false, false_and, ite_false]

/-- Positivity of the source and reflected target separates their quotient
    supports. The full self-adjoint graph consequently pairs exactly its
    decreasing edges; duplicated graph sites are unnecessary for this test. -/
theorem integer_graph_cross_support_entry {ι : Type*} [Fintype ι]
    (site : ι → ℤ) (N : ℕ) (r c : ℤ) (hN : 0 < N)
    (F G : ι → ℝ)
    (hF : ∀ i, F i ≠ 0 → 0 < (N : ℤ) * site i + r)
    (hG : ∀ i, G i ≠ 0 → (N : ℤ) * site i + r < 0)
    (Q : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → Prop) (g center : ℤ → ℝ)
    (L K : ℝ) (extra : ℤ → Prop) (h d : ℕ) (i j : ι) :
    F i * integerEdgeMatrix (fun i => site i + c) Q u eligible g center L K extra h d i j * G j =
      F i * (∑ q ∈ Q, directedIntegerEdge Q u eligible g center L K extra h d q
        (site j + c) (site i + c)) * G j := by
  by_cases hFi : F i = 0
  · simp only [hFi, zero_mul]
  by_cases hGj : G j = 0
  · simp only [hGj, mul_zero]
  have horder : site j < site i := by
    by_contra hnot
    have hij : site i ≤ site j := le_of_not_gt hnot
    have hn : (0 : ℤ) ≤ N := Int.natCast_nonneg _
    have hmono := mul_le_mul_of_nonneg_left hij hn
    have hsource := hF i hFi
    have htarget := hG j hGj
    linarith
  have hmodel : site j + c < site i + c := by omega
  unfold integerEdgeMatrix
  simp only [increasing_edge_zero_below Q u eligible g center L K extra h d _ _ _ hmodel, zero_add]

theorem integer_graph_cross_support_pairing {ι : Type*} [Fintype ι]
    (site : ι → ℤ) (N : ℕ) (r c : ℤ) (hN : 0 < N)
    (F G : ι → ℝ)
    (hF : ∀ i, F i ≠ 0 → 0 < (N : ℤ) * site i + r)
    (hG : ∀ i, G i ≠ 0 → (N : ℤ) * site i + r < 0)
    (Q : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → Prop) (g center : ℤ → ℝ)
    (L K : ℝ) (extra : ℤ → Prop) (h d : ℕ) :
    (∑ i, ∑ j, F i * integerEdgeMatrix (fun i => site i + c) Q u eligible g center L K extra h d i j * G j) =
      ∑ i, ∑ j, F i * (∑ q ∈ Q, directedIntegerEdge Q u eligible g center L K extra h d q
        (site j + c) (site i + c)) * G j := by
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  exact integer_graph_cross_support_entry site N r c hN F G hF hG Q u eligible g center L K extra h d i j

#print axioms integer_graph_cross_support_pairing

end ReflectedLiouville
