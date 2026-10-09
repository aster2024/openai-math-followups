import ReflectedLiouville.ReflectedForms
import ReflectedLiouville.EdgeWeightCancellation

set_option autoImplicit false
open scoped Classical
open OAI.TwoPointCorrelations

namespace ReflectedLiouville

lemma source_test_value_inside (Q : Finset ℕ) (T L : ℝ) (x : ℤ)
    (hx : 0 < x) (hxT : (x : ℝ) ≤ T) :
    sourceTestValue Q T L x = liouvilleAtInteger x * actualPaddingVertex Q x *
      (if actualPaddingDegreeCut Q L x then 1 else 0) := by
  by_cases hc : actualPaddingDegreeCut Q L x <;> simp [sourceTestValue, hx, hxT, hc]

lemma target_test_value_below_cutoff (Q : Finset ℕ) (U L : ℝ) (y : ℤ)
    (hyU : ((-y : ℤ) : ℝ) ≤ U) :
    targetTestValue Q U L y = liouvilleAtInteger (-y) * actualPaddingVertex Q y *
      (if actualPaddingDegreeCut Q L y then 1 else 0) := by
  have hyU' : -(y : ℝ) ≤ U := by simpa only [Int.cast_neg] using hyU
  by_cases hy : y < 0
  · by_cases hc : actualPaddingDegreeCut Q L y <;>
      simp [targetTestValue, sourceTestValue, actualPaddingDegreeCut_neg, actualPaddingVertex_neg, hy, hyU', hc]
  · have hzero : liouvilleAtInteger (-y) = 0 := liouvilleAtInteger_of_nonpos _ (by omega)
    simp [targetTestValue, sourceTestValue, hy, hzero]

/-- One exact reflected kept atom, including center/prohibited endpoint
    masks and both padding cuts, equals its weighted decreasing-edge test. -/
theorem kept_atom_pairing {N J M : ℕ} (data : ProhibitedPrimeFamily N J M)
    (L W T U : ℝ) (eligible : ℕ → ℕ → Prop) (d q : ℕ) (x : ℤ)
    (hq : q ∈ boundedPaddingDivisors data.Q M) (he : eligible d q)
    (hx : 0 < x) (hxT : (x : ℝ) ≤ T) (hstepU : (((N * d * q : ℕ) : ℤ) : ℝ) ≤ U) :
    let y := x - ((N * q * d : ℕ) : ℤ)
    (if (actualPaddingDegree data.P x : ℝ) ≤ 6 * W * J ∧
        (actualPaddingDegree data.P y : ℝ) ≤ 6 * W * J ∧
        ¬ProhibitedSite N ⌊L ^ (1 / 10 : ℝ)⌋₊ (fun d q => (d, q) ∈ data.pairs) x ∧
        ¬ProhibitedSite N ⌊L ^ (1 / 10 : ℝ)⌋₊ (fun d q => (d, q) ∈ data.pairs) y then
      sourceTestValue data.Q T L x *
        directedIntegerEdge (boundedPaddingDivisors data.Q M) actualPaddingCoefficient (eligible d)
          (actualPaddingVertex data.Q) (centeredTuple d.primeFactors) L (Real.exp (4 * J))
          (actualPaddingDegreeCut data.Q L) N d q y x * targetTestValue data.Q U L y else 0) =
      L * keptReflectionAtom data L W eligible (d, q) x := by
  dsimp only
  let y := x - ((N * q * d : ℕ) : ℤ)
  have hxy : x = y + ((N * q * d : ℕ) : ℤ) := by dsimp [y]; ring
  have hstep : ((N * d * q : ℕ) : ℤ) = ((N * q * d : ℕ) : ℤ) := by push_cast; ring
  have hyU : ((-y : ℤ) : ℝ) ≤ U := by
    have hxR : (0 : ℝ) < x := by exact_mod_cast hx
    dsimp [y]
    push_cast at hstepU ⊢
    nlinarith only [hstepU, hxR]
  have hcenter := centered_tuple_at_reflected_endpoint N q d x
  change centeredTuple d.primeFactors y = centeredTuple d.primeFactors x at hcenter
  have hqdiv : (q : ℤ) ∣ y ↔ (q : ℤ) ∣ x := (padding_dvd_along_edge N q d y x hxy).symm
  have hcoef := directed_edge_cancel_tests (boundedPaddingDivisors data.Q M) actualPaddingCoefficient (eligible d)
    (actualPaddingVertex data.Q) (centeredTuple d.primeFactors) L (Real.exp (4 * J))
    (actualPaddingDegreeCut data.Q L) N d q y x (liouvilleAtInteger x) (liouvilleAtInteger (-y))
    (actualPaddingVertex_ne_zero data.Q y) (actualPaddingVertex_ne_zero data.Q x)
  have hreflect : ((N * d * q : ℕ) : ℤ) - x = -y := by rw [hstep]; dsimp [y]; ring
  have hcoef' :
      (actualPaddingVertex data.Q x * liouvilleAtInteger x) *
        directedIntegerEdge (boundedPaddingDivisors data.Q M) actualPaddingCoefficient (eligible d)
          (actualPaddingVertex data.Q) (centeredTuple d.primeFactors) L (Real.exp (4 * J))
          (actualPaddingDegreeCut data.Q L) N d q y x *
          (actualPaddingVertex data.Q y * liouvilleAtInteger (-y)) =
      if (q : ℤ) ∣ x ∧
        integerEdgeKeep (boundedPaddingDivisors data.Q M) actualPaddingCoefficient (eligible d)
          (actualPaddingVertex data.Q) L (Real.exp (4 * J)) (actualPaddingDegreeCut data.Q L) y ∧
        integerEdgeKeep (boundedPaddingDivisors data.Q M) actualPaddingCoefficient (eligible d)
          (actualPaddingVertex data.Q) L (Real.exp (4 * J)) (actualPaddingDegreeCut data.Q L) x then
        L * actualPaddingCoefficient q * centeredTuple d.primeFactors x *
          liouvilleAtInteger x * liouvilleAtInteger (-y) else 0 := by
    simpa only [hq, hxy, he, hqdiv, hcenter, true_and] using hcoef
  rw [source_test_value_inside data.Q T L x hx hxT, target_test_value_below_cutoff data.Q U L y hyU]
  unfold keptReflectionAtom reflectionVertexKeep centeredReflectionAtom
  dsimp only [Prod.fst, Prod.snd]
  simp only [hstep]
  simp only [show x - ((N * q * d : ℕ) : ℤ) = y from rfl]
  have hreflect' : ((N * q * d : ℕ) : ℤ) - x = -y := by dsimp [y]; ring
  rw [hreflect']
  by_cases hPX : (actualPaddingDegree data.P x : ℝ) ≤ 6 * W * J <;>
    by_cases hPY : (actualPaddingDegree data.P y : ℝ) ≤ 6 * W * J <;>
    by_cases hbX : ProhibitedSite N ⌊L ^ (1 / 10 : ℝ)⌋₊ (fun d q => (d, q) ∈ data.pairs) x <;>
    by_cases hbY : ProhibitedSite N ⌊L ^ (1 / 10 : ℝ)⌋₊ (fun d q => (d, q) ∈ data.pairs) y <;>
    simp only [hPX, hPY, hbX, hbY, not_true_eq_false, not_false_eq_true,
      false_and, and_false, true_and, and_true, ite_false, ite_true, mul_zero]
  by_cases hcX : integerEdgeKeep (boundedPaddingDivisors data.Q M) actualPaddingCoefficient (eligible d)
      (actualPaddingVertex data.Q) L (Real.exp (4 * J)) (actualPaddingDegreeCut data.Q L) x <;>
    by_cases hcY : integerEdgeKeep (boundedPaddingDivisors data.Q M) actualPaddingCoefficient (eligible d)
      (actualPaddingVertex data.Q) L (Real.exp (4 * J)) (actualPaddingDegreeCut data.Q L) y
  · have hcutX := hcX.2
    have hcutY := hcY.2
    simp only [hcX, hcY, and_true, true_and, ite_true, hcutX, hcutY, mul_one] at hcoef' ⊢
    by_cases hdv : (q : ℤ) ∣ x <;> simp only [hdv, ite_true, ite_false, mul_zero] at hcoef' ⊢ <;>
      linear_combination hcoef'
  all_goals
    simp only [hcX, hcY, and_false, false_and, ite_false, mul_zero] at hcoef' ⊢
    linear_combination (if actualPaddingDegreeCut data.Q L x then (1 : ℝ) else 0) *
      (if actualPaddingDegreeCut data.Q L y then (1 : ℝ) else 0) * hcoef'

#print axioms kept_atom_pairing

end ReflectedLiouville
