import ReflectedLiouville.RealMatrixPairing

set_option autoImplicit false
open scoped BigOperators Classical
open OAI.TwoPointCorrelations

namespace ReflectedLiouville

lemma matrixOperator_sum_real {V α : Type*} [Fintype V] [DecidableEq V]
    [Fintype α] (A : α → V → V → ℝ) :
    (∑ a, matrixOperator (fun i j => (A a i j : ℂ))) =
      matrixOperator (fun i j => ((∑ a, A a i j : ℝ) : ℂ)) := by
  ext v i
  simp only [ContinuousLinearMap.sum_apply, WithLp.ofLp_sum, Finset.sum_apply, matrixOperator_apply, Complex.ofReal_sum,
    Finset.sum_mul]
  exact Finset.sum_comm (f := fun a j => (A a i j : ℂ) * v j)

lemma sourceTestValue_support (Q : Finset ℕ) (T L : ℝ) (x : ℤ)
    (hx : sourceTestValue Q T L x ≠ 0) : 0 < x ∧ (x : ℝ) ≤ T := by
  by_contra hn
  apply hx
  unfold sourceTestValue
  rw [if_neg (by tauto)]

lemma targetTestValue_support (Q : Finset ℕ) (T L : ℝ) (x : ℤ)
    (hx : targetTestValue Q T L x ≠ 0) : x < 0 ∧ ((-x : ℤ) : ℝ) ≤ T := by
  have h := sourceTestValue_support Q T L (-x) hx
  constructor
  · omega
  · exact h.2

/-- Exact coordinate formula for the physical compression against the
    reflected tests, before collapsing the forced target and residue sums. -/
theorem physical_scalar_pairing {N J M : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (data : ProhibitedPrimeFamily N J M) (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (hUnion : Finset.univ.biUnion P = data.P)
    (site : V → ℤ) (r : ℤ) (L W T U : ℝ) (eligible : ℕ → ℕ → Prop) :
    let physical := fun i => (N : ℤ) * site i + r
    inner ℂ (sourceTestVector data.Q T L physical)
      (physicalReflectionCompression data P site r L W eligible (targetTestVector data.Q U L physical)) =
      ((∑ d : (j : Fin J) → P j, ∑ i : V, ∑ j : V,
        if (actualPaddingDegree data.P (physical i) : ℝ) ≤ 6 * W * J ∧
          (actualPaddingDegree data.P (physical j) : ℝ) ≤ 6 * W * J ∧
          ¬ProhibitedSite N ⌊L ^ (1 / 10 : ℝ)⌋₊ (fun d q => (d,q) ∈ data.pairs) (physical i) ∧
          ¬ProhibitedSite N ⌊L ^ (1 / 10 : ℝ)⌋₊ (fun d q => (d,q) ∈ data.pairs) (physical j) then
          sourceTestValue data.Q T L (physical i) *
            (∑ q ∈ boundedPaddingDivisors data.Q M,
              directedIntegerEdge (boundedPaddingDivisors data.Q M) actualPaddingCoefficient
                (eligible (∏ k, (d k).val)) (actualPaddingVertex data.Q)
                (centeredTuple (∏ k, (d k).val).primeFactors) L (Real.exp (4 * J))
                (actualPaddingDegreeCut data.Q L) N (∏ k, (d k).val) q (physical j) (physical i)) *
            targetTestValue data.Q U L (physical j) else 0 : ℝ) : ℂ) := by
  dsimp only
  let physical := fun i : V => (N : ℤ) * site i + r
  let gate := fun (_ : ℕ) (i j : V) =>
    ¬ProhibitedSite N ⌊L ^ (1 / 10 : ℝ)⌋₊ (fun d q => (d,q) ∈ data.pairs) (physical i) ∧
    ¬ProhibitedSite N ⌊L ^ (1 / 10 : ℝ)⌋₊ (fun d q => (d,q) ∈ data.pairs) (physical j)
  let A : ((j : Fin J) → P j) → V → V → ℝ := primeRealEdgeMatrix P physical (boundedPaddingDivisors data.Q M)
    actualPaddingCoefficient eligible (actualPaddingVertex data.Q) L (Real.exp (4 * J))
    (fun _ => actualPaddingDegreeCut data.Q L) N gate
  have hOp := fun d => primeFamilyGraphOperator_eq_realMatrix P hprime hdisjoint physical
    (boundedPaddingDivisors data.Q M) actualPaddingCoefficient eligible (actualPaddingVertex data.Q)
    L (Real.exp (4 * J)) (fun _ => actualPaddingDegreeCut data.Q L) N gate d
  have hComp : physicalReflectionCompression data P site r L W eligible =
      coordinateProjection (fun i : V => (actualPaddingDegree data.P (physical i) : ℝ) ≤ 6 * W * J) *
        matrixOperator (fun i j => ((∑ d, A d i j : ℝ) : ℂ)) *
      coordinateProjection (fun i : V => (actualPaddingDegree data.P (physical i) : ℝ) ≤ 6 * W * J) := by
    unfold physicalReflectionCompression
    dsimp only
    rw [hUnion]
    congr 1
    congr 1
    calc
      _ = ∑ d, matrixOperator (fun i j => (A d i j : ℂ)) :=
        Finset.sum_congr rfl (fun d _ => hOp d)
      _ = _ := matrixOperator_sum_real A
  rw [hComp]
  unfold sourceTestVector targetTestVector
  rw [projected_real_matrix_inner]
  congr 1
  change (∑ i : V, ∑ j : V, if (actualPaddingDegree data.P (physical i) : ℝ) ≤ 6 * W * J ∧
    (actualPaddingDegree data.P (physical j) : ℝ) ≤ 6 * W * J then
    sourceTestValue data.Q T L (physical i) * (∑ d, A d i j) * targetTestValue data.Q U L (physical j) else 0) = _
  simp only [Finset.mul_sum, Finset.sum_mul]
  have hif (b : Prop) (f : ((j : Fin J) → P j) → ℝ) :
      (if b then ∑ d, f d else 0) = ∑ d, if b then f d else 0 := by
    by_cases hb : b <;> simp [hb]
  have hdist : (∑ i : V, ∑ j : V, if (actualPaddingDegree data.P (physical i) : ℝ) ≤ 6 * W * J ∧
      (actualPaddingDegree data.P (physical j) : ℝ) ≤ 6 * W * J then
      (∑ d, sourceTestValue data.Q T L (physical i) * A d i j * targetTestValue data.Q U L (physical j)) else 0) =
      ∑ i : V, ∑ j : V, ∑ d : (k : Fin J) → P k,
        if (actualPaddingDegree data.P (physical i) : ℝ) ≤ 6 * W * J ∧
          (actualPaddingDegree data.P (physical j) : ℝ) ≤ 6 * W * J then
          sourceTestValue data.Q T L (physical i) * A d i j * targetTestValue data.Q U L (physical j) else 0 := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hb : (actualPaddingDegree data.P (physical i) : ℝ) ≤ 6 * W * J ∧
      (actualPaddingDegree data.P (physical j) : ℝ) ≤ 6 * W * J <;> simp [hb]
  rw [hdist]
  have hswap (F : V → V → ((j : Fin J) → P j) → ℝ) :
      (∑ i, ∑ j, ∑ d, F i j d) = ∑ d, ∑ i, ∑ j, F i j d := by
    calc
      _ = ∑ i, ∑ d, ∑ j, F i j d := Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
      _ = _ := Finset.sum_comm
  rw [hswap]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  dsimp only [physical] at *
  by_cases hF : sourceTestValue data.Q T L ((N : ℤ) * site i + r) = 0
  · simp [physical, hF, A, primeRealEdgeMatrix]
  by_cases hG : targetTestValue data.Q U L ((N : ℤ) * site j + r) = 0
  · simp [physical, hG, A, primeRealEdgeMatrix]
  have hij : physical j < physical i :=
    (targetTestValue_support _ _ _ _ hG).1.trans (sourceTestValue_support _ _ _ _ hF).1
  have hinc (q : ℕ) := increasing_edge_zero_below (boundedPaddingDivisors data.Q M)
    actualPaddingCoefficient (eligible (∏ k, (d k).val)) (actualPaddingVertex data.Q)
    (centeredTuple (∏ k, (d k).val).primeFactors) L (Real.exp (4 * J))
    (actualPaddingDegreeCut data.Q L) N (∏ k, (d k).val) q (physical i) (physical j) hij
  dsimp only [A, primeRealEdgeMatrix, physical]
  dsimp only [physical] at hinc
  simp only [integerEdgeMatrix, hinc, zero_add]
  dsimp only [gate]
  split_ifs <;> simp_all only [physical, and_self, ite_true, ite_false, mul_zero, zero_mul,
    Finset.mul_sum, Finset.sum_mul] <;> tauto

#print axioms physical_scalar_pairing

end ReflectedLiouville
