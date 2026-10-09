import ReflectedLiouville.TestEnergyBound
import OAI.NumberTheory.TwoPoint.Bounds.GraphTesting

set_option autoImplicit false
open scoped BigOperators Classical
open OAI.TwoPointCorrelations

namespace ReflectedLiouville

lemma weighted_matrix_bilinear_le {V : Type*} [Fintype V] [DecidableEq V]
    (A : V → V → ℂ) (g R : V → ℝ) (hg : ∀ i, 0 < g i)
    (v w : EuclideanSpace ℂ V) (hv : ∀ i, ‖v i‖ ≤ g i) (hw : ∀ i, ‖w i‖ ≤ g i)
    (hrow : ∀ i, v i ≠ 0 → ∑ j, ‖A i j‖ * g j / g i ≤ R i) :
    ‖inner ℂ v (matrixOperator A w)‖ ≤ ∑ i, if v i = 0 then 0 else R i * (g i) ^ 2 := by
  rw [PiLp.inner_apply]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  by_cases hvi : v i = 0
  · simp [hvi]
  · rw [ite_eq_right hvi]
    calc
      _ ≤ ‖v i‖ * ‖matrixOperator A w i‖ := norm_inner_le_norm _ _
      _ ≤ g i * (∑ j, ‖A i j‖ * g j) := by
        apply mul_le_mul (hv i) _ (norm_nonneg _) (hg i).le
        rw [matrixOperator_apply]
        apply (norm_sum_le _ _).trans
        exact Finset.sum_le_sum (fun j _ => by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hw j) (norm_nonneg _))
      _ = (∑ j, ‖A i j‖ * g j / g i) * (g i) ^ 2 := by
        rw [← Finset.sum_div]
        field_simp [(hg i).ne']
      _ ≤ _ := mul_le_mul_of_nonneg_right (hrow i hvi) (sq_nonneg _)

lemma weighted_matrix_bilinear_support {V : Type*} [Fintype V] [DecidableEq V]
    (A : V → V → ℂ) (g : V → ℝ) (R G : ℝ)
    (hg : ∀ i, 0 < g i) (hR : 0 ≤ R) (hG : 0 ≤ G)
    (v w : EuclideanSpace ℂ V) (hv : ∀ i, ‖v i‖ ≤ g i) (hw : ∀ i, ‖w i‖ ≤ g i)
    (hrow : ∀ i, v i ≠ 0 → ∑ j, ‖A i j‖ * g j / g i ≤ R)
    (hweight : ∀ i, v i ≠ 0 → (g i) ^ 2 ≤ G)
    (S : Finset V) (hzero : ∀ i, i ∉ S → v i = 0) :
    ‖inner ℂ v (matrixOperator A w)‖ ≤ (S.card : ℝ) * R * G := by
  apply (weighted_matrix_bilinear_le A g (fun _ => R) hg v w hv hw hrow).trans
  calc
    _ ≤ ∑ i, if i ∈ S then R * G else 0 := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hS : i ∈ S
      · rw [ite_eq_left hS]
        by_cases hvi : v i = 0
        · rw [ite_eq_left hvi]
          exact mul_nonneg hR hG
        · rw [ite_eq_right hvi]
          exact mul_le_mul_of_nonneg_left (hweight i hvi) hR
      · rw [ite_eq_right hS, ite_eq_left (hzero i hS)]
    _ = _ := by simp; ring

/-- The bad-origin estimate pays only the actual support cardinality, rather
    than the exponentially larger ambient block. -/
theorem prime_graph_sparse_bilinear {J : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (P : Fin J → Finset ℕ) (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (site : V → ℤ) (hinj : Function.Injective site)
    (Q : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (g : ℤ → ℝ) (L K W : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ)
    (gate : ℕ → V → V → Prop) (hL : 0 < L) (hK : 0 ≤ K) (hW : 0 ≤ W)
    (hu : ∀ q ∈ Q, 0 ≤ u q) (hg : ∀ n, 0 < g n)
    (hV : ∀ j, primeHarmonicMass (P j) ≤ 2 * W)
    (v w : EuclideanSpace ℂ V) (hv : ∀ i, ‖v i‖ ≤ g (site i)) (hw : ∀ i, ‖w i‖ ≤ g (site i))
    (hdegree : ∀ i, v i ≠ 0 → (actualPaddingDegree (Finset.univ.biUnion P) (site i) : ℝ) ≤ 6 * W * J)
    (G : ℝ) (hG : 0 ≤ G) (hweight : ∀ i, v i ≠ 0 → (g (site i)) ^ 2 ≤ G)
    (S : Finset V) (hzero : ∀ i, i ∉ S → v i = 0) :
    ‖inner ℂ v ((∑ d, primeFamilyGraphOperator (fun j (p : P j) => p.val) (fun _ _ => 0)
      site Q u eligible g L K extra h gate d) w)‖ ≤
        (S.card : ℝ) * (2 * K * (8 * W) ^ J) * G := by
  let A (d : (j : Fin J) → P j) := maskedIntegerEdgeMatrix site Q u
    (eligible (familyTuple (fun j (p : P j) => p.val) d)) g
    (familyCenter (fun j (p : P j) => p.val) (fun _ _ => 0) d) L K
    (extra (familyTuple (fun j (p : P j) => p.val) d)) h
    (familyTuple (fun j (p : P j) => p.val) d) (gate (familyTuple (fun j (p : P j) => p.val) d))
  have hrow (i : V) (hi : v i ≠ 0) :
      (∑ j, ‖∑ d, A d i j‖ * g (site j) / g (site i)) ≤ 2 * K * (8 * W) ^ J := by
    calc
      _ ≤ ∑ j, (∑ d, ‖A d i j‖) * g (site j) / g (site i) := by
        apply Finset.sum_le_sum
        intro j hj
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (norm_sum_le _ _) (hg _).le) (hg _).le
      _ = ∑ d, ∑ j, ‖A d i j‖ * g (site j) / g (site i) := by
        simp only [Finset.sum_mul, Finset.sum_div]
        rw [Finset.sum_comm]
      _ ≤ ∑ d : (j : Fin J) → P j,
          2 * K * |familyCenter (fun j (p : P j) => p.val) (fun _ _ => 0) d (site i)| := by
        apply Finset.sum_le_sum
        intro d hd
        exact maskedIntegerEdgeMatrix_weighted_row site hinj Q u _ g _ L K _ h _ _
          hL hK hu hg (fun q _ n => familyCenter_padding_periodic _ _ d h q n) i
      _ = 2 * K * ∑ d : (j : Fin J) → P j,
          |familyCenter (fun j (p : P j) => p.val) (fun _ _ => 0) d (site i)| := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (sum_familyCenter_abs_le P hprime hdisjoint (site i) W hV (hdegree i hi)) (by positivity)
  have ht := weighted_matrix_bilinear_support (fun i j => ∑ d, A d i j)
    (fun i => g (site i)) (2 * K * (8 * W) ^ J) G (fun i => hg _) (by positivity) hG
    v w hv hw hrow hweight S hzero
  rw [matrixOperator_sum] at ht
  exact ht

#print axioms prime_graph_sparse_bilinear

end ReflectedLiouville
