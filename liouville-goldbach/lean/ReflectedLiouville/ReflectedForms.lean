import ReflectedLiouville.KeptOperatorBound

set_option autoImplicit false
open scoped BigOperators Classical
open OAI.TwoPointCorrelations

namespace ReflectedLiouville

noncomputable def reflectionVertexKeep {N J M : ℕ} (data : ProhibitedPrimeFamily N J M)
    (L W : ℝ) (eligible : ℕ → ℕ → Prop) (d : ℕ) (n : ℤ) : Prop :=
  integerEdgeKeep (boundedPaddingDivisors data.Q M) actualPaddingCoefficient (eligible d)
    (actualPaddingVertex data.Q) L (Real.exp (4 * J)) (actualPaddingDegreeCut data.Q L) n ∧
      (actualPaddingDegree data.P n : ℝ) ≤ 6 * W * J ∧
        ¬ProhibitedSite N ⌊L ^ (1 / 10 : ℝ)⌋₊ (fun d q => (d, q) ∈ data.pairs) n

noncomputable def centeredReflectionAtom (N : ℕ) (dq : ℕ × ℕ) (n : ℤ) : ℝ :=
  if (dq.2 : ℤ) ∣ n then actualPaddingCoefficient dq.2 * centeredTuple dq.1.primeFactors n *
    liouvilleAtInteger n * liouvilleAtInteger (((N * dq.1 * dq.2 : ℕ) : ℤ) - n) else 0

noncomputable def keptReflectionAtom {N J M : ℕ} (data : ProhibitedPrimeFamily N J M)
    (L W : ℝ) (eligible : ℕ → ℕ → Prop) (dq : ℕ × ℕ) (n : ℤ) : ℝ :=
  if reflectionVertexKeep data L W eligible dq.1 n ∧
      reflectionVertexKeep data L W eligible dq.1 (n - ((N * dq.1 * dq.2 : ℕ) : ℤ)) then
    centeredReflectionAtom N dq n else 0

noncomputable def centeredBinForm (I : Finset (ℕ × ℕ)) (N : ℕ) (η : ℝ) (j : ℤ) : ℝ :=
  (∑ dq ∈ I.filter (fun dq => reflectionPairBin η dq = j),
    ∑ x ∈ Finset.Icc 1 ⌊reflectionBinCutoff N η j⌋₊, centeredReflectionAtom N dq (x : ℤ)) /
      reflectionBinCutoff N η j

noncomputable def keptCenteredBinForm {N J M : ℕ} (data : ProhibitedPrimeFamily N J M)
    (L W η : ℝ) (j : ℤ) : ℝ :=
  (∑ dq ∈ data.pairs.filter (fun dq => reflectionPairBin η dq = j),
    ∑ x ∈ Finset.Icc 1 ⌊reflectionBinCutoff N η j⌋₊,
      keptReflectionAtom data L W (binPairEligible data.pairs η j) dq (x : ℤ)) /
        reflectionBinCutoff N η j

lemma centeredReflectionAtom_positive_bound (N : ℕ) (dq : ℕ × ℕ) (n : ℤ) :
    |centeredReflectionAtom N dq n| ≤ actualPaddingCoefficient dq.2 * positivePrimeWeight dq.1.primeFactors n := by
  have hu : 0 ≤ actualPaddingCoefficient dq.2 := actualPaddingCoefficient_nonneg _
  have hP : 0 ≤ positivePrimeWeight dq.1.primeFactors n := positivePrimeWeight_nonneg _ _
  unfold centeredReflectionAtom
  split_ifs
  · rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hu]
    have hc := abs_centeredTuple_le_positivePrimeWeight dq.1.primeFactors n
    have hl1 := abs_liouvilleAtInteger_le n
    have hl2 := abs_liouvilleAtInteger_le (((N * dq.1 * dq.2 : ℕ) : ℤ) - n)
    calc
      _ ≤ (actualPaddingCoefficient dq.2 * positivePrimeWeight dq.1.primeFactors n) * 1 * 1 := by
        apply mul_le_mul
        · apply mul_le_mul
          · exact mul_le_mul_of_nonneg_left hc hu
          · exact hl1
          · exact abs_nonneg _
          · exact mul_nonneg hu hP
        · exact hl2
        · exact abs_nonneg _
        · exact mul_nonneg (mul_nonneg hu hP) zero_le_one
      _ = _ := by ring
  · simp only [abs_zero]
    exact mul_nonneg hu hP

/-- Two-endpoint positive deletion envelope, before any model comparison.
    The target predicate remains at the negative physical graph site. -/
theorem reflected_atom_deletion_envelope {N J M : ℕ} (data : ProhibitedPrimeFamily N J M)
    (L W : ℝ) (eligible : ℕ → ℕ → Prop) (dq : ℕ × ℕ) (n : ℤ) :
    |centeredReflectionAtom N dq n - keptReflectionAtom data L W eligible dq n| ≤
      actualPaddingCoefficient dq.2 * positivePrimeWeight dq.1.primeFactors n *
        ((if ¬reflectionVertexKeep data L W eligible dq.1 n then 1 else 0) +
          (if ¬reflectionVertexKeep data L W eligible dq.1 (n - ((N * dq.1 * dq.2 : ℕ) : ℤ)) then 1 else 0)) := by
  have hb := centeredReflectionAtom_positive_bound N dq n
  have hn : 0 ≤ actualPaddingCoefficient dq.2 * positivePrimeWeight dq.1.primeFactors n :=
    mul_nonneg (actualPaddingCoefficient_nonneg _) (positivePrimeWeight_nonneg _ _)
  by_cases hs : reflectionVertexKeep data L W eligible dq.1 n <;>
    by_cases ht : reflectionVertexKeep data L W eligible dq.1 (n - ((N * dq.1 * dq.2 : ℕ) : ℤ)) <;>
    simp only [keptReflectionAtom, hs, ht, and_true, true_and, and_false, false_and,
      not_true_eq_false, not_false_eq_true, ite_true, ite_false, sub_zero, sub_self, abs_zero] <;>
    nlinarith only [hb, hn]

#print axioms reflected_atom_deletion_envelope

end ReflectedLiouville
