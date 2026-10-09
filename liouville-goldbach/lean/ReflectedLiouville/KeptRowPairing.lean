import ReflectedLiouville.ForcedEdgePairing
import ReflectedLiouville.PhysicalPrefixExact

set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped BigOperators Classical
open OAI.TwoPointCorrelations

namespace ReflectedLiouville

noncomputable def reflectionCenterKeep {N J M : ℕ} (data : ProhibitedPrimeFamily N J M)
    (L W : ℝ) (x : ℤ) : Prop :=
  (actualPaddingDegree data.P x : ℝ) ≤ 6 * W * J ∧
    ¬ProhibitedSite N ⌊L ^ (1 / 10 : ℝ)⌋₊ (fun d q => (d,q) ∈ data.pairs) x

/-- The full target-coordinate sum equals the eligible kept atoms at one
    source site. No target coverage is requested for a zero test value. -/
theorem kept_row_pairing {N J M : ℕ} {V : Type*} [Fintype V]
    (data : ProhibitedPrimeFamily N J M) (physical : V → ℤ) (hinj : Function.Injective physical)
    (L W T U : ℝ) (eligible : ℕ → ℕ → Prop) (d : ℕ) (x : ℤ)
    (hcover : ∀ q ∈ boundedPaddingDivisors data.Q M,
      targetTestValue data.Q U L (x - ((N*q*d : ℕ) : ℤ)) ≠ 0 →
        ∃ i, physical i = x - ((N*q*d : ℕ) : ℤ))
    (hstepU : ∀ q ∈ boundedPaddingDivisors data.Q M, eligible d q →
      (((N * d * q : ℕ) : ℤ) : ℝ) ≤ U) :
    (∑ i : V, if reflectionCenterKeep data L W x ∧ reflectionCenterKeep data L W (physical i) then
      sourceTestValue data.Q T L x *
        (∑ q ∈ boundedPaddingDivisors data.Q M,
          directedIntegerEdge (boundedPaddingDivisors data.Q M) actualPaddingCoefficient (eligible d)
            (actualPaddingVertex data.Q) (centeredTuple d.primeFactors) L (Real.exp (4 * J))
            (actualPaddingDegreeCut data.Q L) N d q (physical i) x) *
        targetTestValue data.Q U L (physical i) else 0) =
      if 0 < x ∧ (x : ℝ) ≤ T then
        ∑ q ∈ boundedPaddingDivisors data.Q M, if eligible d q then
          L * keptReflectionAtom data L W eligible (d,q) x else 0 else 0 := by
  have hc : ∀ q ∈ boundedPaddingDivisors data.Q M,
      (if reflectionCenterKeep data L W x ∧ reflectionCenterKeep data L W (x - ((N*q*d : ℕ) : ℤ)) then
        sourceTestValue data.Q T L x *
          directedIntegerEdge (boundedPaddingDivisors data.Q M) actualPaddingCoefficient (eligible d)
            (actualPaddingVertex data.Q) (centeredTuple d.primeFactors) L (Real.exp (4 * J))
            (actualPaddingDegreeCut data.Q L) N d q (x - ((N*q*d : ℕ) : ℤ)) x *
          targetTestValue data.Q U L (x - ((N*q*d : ℕ) : ℤ)) else 0) ≠ 0 →
        ∃ i, physical i = x - ((N*q*d : ℕ) : ℤ) := by
    intro q hq hn
    apply hcover q hq
    intro hz
    apply hn
    simp only [hz, mul_zero, ite_self]
  rw [masked_directed_edge_pairing physical hinj (boundedPaddingDivisors data.Q M)
    actualPaddingCoefficient (eligible d) (actualPaddingVertex data.Q) (centeredTuple d.primeFactors)
    L (Real.exp (4 * J)) (actualPaddingDegreeCut data.Q L) (reflectionCenterKeep data L W)
    N d x (sourceTestValue data.Q T L x) (targetTestValue data.Q U L) hc]
  by_cases hx : 0 < x ∧ (x : ℝ) ≤ T
  · rw [ite_eq_left hx]
    apply Finset.sum_congr rfl
    intro q hq
    by_cases he : eligible d q
    · rw [ite_eq_left he]
      have hpair := kept_atom_pairing data L W T U eligible d q x hq he hx.1 hx.2 (hstepU q hq he)
      dsimp only at hpair
      have hgate : (reflectionCenterKeep data L W x ∧
          reflectionCenterKeep data L W (x - ((N*q*d : ℕ) : ℤ))) ↔
          (actualPaddingDegree data.P x : ℝ) ≤ 6 * W * J ∧
          (actualPaddingDegree data.P (x - ((N*q*d : ℕ) : ℤ)) : ℝ) ≤ 6 * W * J ∧
          ¬ProhibitedSite N ⌊L ^ (1 / 10 : ℝ)⌋₊ (fun d q => (d,q) ∈ data.pairs) x ∧
          ¬ProhibitedSite N ⌊L ^ (1 / 10 : ℝ)⌋₊ (fun d q => (d,q) ∈ data.pairs) (x - ((N*q*d : ℕ) : ℤ)) := by
        unfold reflectionCenterKeep
        tauto
      simpa only [hgate] using hpair
    · simp only [he, ite_false]
      have hz : directedIntegerEdge (boundedPaddingDivisors data.Q M) actualPaddingCoefficient (eligible d)
          (actualPaddingVertex data.Q) (centeredTuple d.primeFactors) L (Real.exp (4 * J))
          (actualPaddingDegreeCut data.Q L) N d q (x - ((N*q*d : ℕ) : ℤ)) x = 0 := by
        simp only [directedIntegerEdge, he, false_and, and_false, ite_false]
      simp only [hz, mul_zero, zero_mul, ite_self]
  · have hz : sourceTestValue data.Q T L x = 0 := by
      unfold sourceTestValue
      rw [ite_eq_right (by tauto)]
    simp only [hx, ite_false, hz, zero_mul, ite_self, Finset.sum_const_zero]

#print axioms kept_row_pairing
end ReflectedLiouville
