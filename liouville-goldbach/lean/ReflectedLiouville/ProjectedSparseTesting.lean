import ReflectedLiouville.SparseGraphTesting
import OAI.NumberTheory.TwoPoint.Bounds.ProjectedGraphTesting

set_option autoImplicit false
open scoped BigOperators Classical
open OAI.TwoPointCorrelations

namespace ReflectedLiouville

/-- Bilinear deterministic testing on the actual source support, retaining
    the original two degree cuts and square-root padding normalization. -/
theorem projected_padding_sparse_bilinear {J : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (P : Fin J → Finset ℕ) (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (site : V → ℤ) (hinj : Function.Injective site)
    (Q Qp : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (L K W : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ) (gate : ℕ → V → V → Prop)
    (hL : 0 < L) (hK : 0 ≤ K) (hW : 0 ≤ W) (hu : ∀ q ∈ Q, 0 ≤ u q)
    (hV : ∀ j, primeHarmonicMass (P j) ≤ 2 * W)
    (f g : ℤ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) (hg : ∀ n, ‖g n‖ ≤ 1)
    (S : Finset V) (hzero : ∀ i, i ∉ S → f (site i) = 0) :
    let B := primeFamilyGraphOperator (fun j (p : P j) => p.val) (fun _ _ => 0)
      site Q u eligible (actualPaddingVertex Qp) L K extra h gate
    let proj := coordinateProjection (fun i : V =>
      (actualPaddingDegree (Finset.univ.biUnion P) (site i) : ℝ) ≤ 6 * W * J)
    let v := paddingTestVector Qp L site f
    let w := paddingTestVector Qp L site g
    ‖inner ℂ v ((proj * (∑ d, B d) * proj) w)‖ ≤
      (S.card : ℝ) * (2 * K * (8 * W) ^ J) * (5 : ℝ) ^ (400 * Real.log L) := by
  dsimp only
  let keep := fun i : V => (actualPaddingDegree (Finset.univ.biUnion P) (site i) : ℝ) ≤ 6 * W * J
  let proj := coordinateProjection keep
  let v := paddingTestVector Qp L site f
  let w := paddingTestVector Qp L site g
  have hcoordV (i : V) : ‖proj v i‖ ≤ actualPaddingVertex Qp (site i) := by
    dsimp only [proj]
    rw [coordinateProjection_apply]
    split_ifs
    · exact paddingTestVector_apply_norm_le Qp L site f hf i
    · simpa only [norm_zero] using (actualPaddingVertex_pos Qp (site i)).le
  have hcoordW (i : V) : ‖proj w i‖ ≤ actualPaddingVertex Qp (site i) := by
    dsimp only [proj]
    rw [coordinateProjection_apply]
    split_ifs
    · exact paddingTestVector_apply_norm_le Qp L site g hg i
    · simpa only [norm_zero] using (actualPaddingVertex_pos Qp (site i)).le
  have hsupp (i : V) (hi : proj v i ≠ 0) : keep i ∧ actualPaddingDegreeCut Qp L (site i) :=
    projected_paddingTestVector_support Qp L site f keep i hi
  have hzero' : ∀ i, i ∉ S → proj v i = 0 := by
    intro i hi
    simp [proj, v, coordinateProjection_apply, paddingTestVector, hzero i hi]
  have hb := prime_graph_sparse_bilinear P hprime hdisjoint site hinj Q u eligible
    (actualPaddingVertex Qp) L K W extra h gate hL hK hW hu (actualPaddingVertex_pos Qp) hV
    (proj v) (proj w) hcoordV hcoordW (fun i hi => (hsupp i hi).1)
    ((5 : ℝ) ^ (400 * Real.log L)) (Real.rpow_nonneg (by norm_num) _)
    (fun i hi => paddingVertex_cut_bound Qp L (site i) (hsupp i hi).2) S hzero'
  have he := (coordinateProjection_selfAdjoint keep).isSymmetric v
    ((∑ d, primeFamilyGraphOperator (fun j (p : P j) => p.val) (fun _ _ => 0)
      site Q u eligible (actualPaddingVertex Qp) L K extra h gate d) (proj w))
  change inner ℂ (proj v) _ = inner ℂ v (proj _) at he
  exact (le_of_eq (congrArg norm he.symm)).trans hb

#print axioms projected_padding_sparse_bilinear

end ReflectedLiouville
