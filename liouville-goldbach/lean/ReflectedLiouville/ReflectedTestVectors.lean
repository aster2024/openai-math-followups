import ReflectedLiouville.PhysicalVolume

set_option autoImplicit false
open scoped BigOperators Classical
open OAI.TwoPointCorrelations

namespace ReflectedLiouville

noncomputable def truncatedPaddingWeight (Q : Finset ℕ) (L : ℝ) (n : ℤ) : ℝ :=
  (actualPaddingVertex Q n) ^ 2 * if actualPaddingDegreeCut Q L n then 1 else 0

lemma truncatedPaddingWeight_nonneg (Q : Finset ℕ) (L : ℝ) (n : ℤ) :
    0 ≤ truncatedPaddingWeight Q L n := by
  unfold truncatedPaddingWeight
  apply mul_nonneg (sq_nonneg _)
  split_ifs <;> norm_num

noncomputable def sourceTestValue (Q : Finset ℕ) (T L : ℝ) (n : ℤ) : ℝ :=
  if 0 < n ∧ (n : ℝ) ≤ T ∧ actualPaddingDegreeCut Q L n then
    liouvilleAtInteger n * actualPaddingVertex Q n else 0

noncomputable def targetTestValue (Q : Finset ℕ) (T L : ℝ) (n : ℤ) : ℝ := sourceTestValue Q T L (-n)

lemma liouvilleAtInteger_sq_of_pos (n : ℤ) (hn : 0 < n) : liouvilleAtInteger n ^ 2 = 1 := by
  have hnp : 0 < n.toNat := by
    have hc := Int.toNat_of_nonneg hn.le
    omega
  exact liouvilleReal_sq hnp.ne'

lemma sourceTestValue_sq (Q : Finset ℕ) (T L : ℝ) (n : ℤ) :
    sourceTestValue Q T L n ^ 2 =
      if 0 < n ∧ (n : ℝ) ≤ T then truncatedPaddingWeight Q L n else 0 := by
  by_cases hr : 0 < n ∧ (n : ℝ) ≤ T
  · by_cases hc : actualPaddingDegreeCut Q L n
    · simp only [sourceTestValue, hr.1, hr.2, hc, and_self, ite_true, mul_pow,
        liouvilleAtInteger_sq_of_pos n hr.1, one_mul, truncatedPaddingWeight, mul_one]
    · simp [sourceTestValue, hr, hc, truncatedPaddingWeight]
  · simp [sourceTestValue, hr, truncatedPaddingWeight, show ¬(0 < n ∧ (n : ℝ) ≤ T ∧ actualPaddingDegreeCut Q L n) by tauto]

noncomputable def sourceTestVector {V : Type*} [Fintype V]
    (Q : Finset ℕ) (T L : ℝ) (physical : V → ℤ) : EuclideanSpace ℂ V :=
  WithLp.toLp 2 (fun i => (sourceTestValue Q T L (physical i) : ℂ))

noncomputable def targetTestVector {V : Type*} [Fintype V]
    (Q : Finset ℕ) (T L : ℝ) (physical : V → ℤ) : EuclideanSpace ℂ V :=
  WithLp.toLp 2 (fun i => (targetTestValue Q T L (physical i) : ℂ))

lemma sourceTestVector_norm_sq {V : Type*} [Fintype V]
    (Q : Finset ℕ) (T L : ℝ) (physical : V → ℤ) :
    ‖sourceTestVector Q T L physical‖ ^ 2 =
      ∑ i, if 0 < physical i ∧ (physical i : ℝ) ≤ T then truncatedPaddingWeight Q L (physical i) else 0 := by
  rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i hi
  change ‖(sourceTestValue Q T L (physical i) : ℂ)‖ ^ 2 = _
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, sourceTestValue_sq]

lemma targetTestVector_norm_sq {V : Type*} [Fintype V]
    (Q : Finset ℕ) (T L : ℝ) (physical : V → ℤ) :
    ‖targetTestVector Q T L physical‖ ^ 2 =
      ∑ i, if 0 < -physical i ∧ (-physical i : ℝ) ≤ T then truncatedPaddingWeight Q L (-physical i) else 0 := by
  simpa only [targetTestVector, targetTestValue, sourceTestVector, Int.cast_neg] using
    sourceTestVector_norm_sq Q T L (fun i => -physical i)

theorem source_test_energy_to_interval {V : Type*} [Fintype V]
    (N : ℕ) (hN : 0 < N) (site : V → ℤ) (hinj : Function.Injective site)
    (Q : Finset ℕ) (T L : ℝ) :
    (∑ r : Fin N, ‖sourceTestVector Q T L (fun i => (N : ℤ) * site i + ((r.val + 1 : ℕ) : ℤ))‖ ^ 2) ≤
      ∑ n ∈ Finset.Icc 1 ⌊T⌋₊, truncatedPaddingWeight Q L (n : ℤ) := by
  simp only [sourceTestVector_norm_sq]
  have hb := bounded_integer_sum_le ((Finset.univ : Finset (Fin N)) ×ˢ (Finset.univ : Finset V))
    (fun ri => (N : ℤ) * site ri.2 + ((ri.1.val + 1 : ℕ) : ℤ))
    (physical_residue_sites_injective N hN site hinj) T (truncatedPaddingWeight Q L)
    (truncatedPaddingWeight_nonneg Q L)
  simpa only [Finset.sum_product, Int.cast_neg] using hb

theorem target_test_energy_to_interval {V : Type*} [Fintype V]
    (N : ℕ) (hN : 0 < N) (site : V → ℤ) (hinj : Function.Injective site)
    (Q : Finset ℕ) (T L : ℝ) :
    (∑ r : Fin N, ‖targetTestVector Q T L (fun i => (N : ℤ) * site i + ((r.val + 1 : ℕ) : ℤ))‖ ^ 2) ≤
      ∑ n ∈ Finset.Icc 1 ⌊T⌋₊, truncatedPaddingWeight Q L (n : ℤ) := by
  simp only [targetTestVector_norm_sq]
  have hphi := physical_residue_sites_injective N hN site hinj
  have hneg : Function.Injective (fun ri : Fin N × V => -((N : ℤ) * site ri.2 + ((ri.1.val + 1 : ℕ) : ℤ))) := by
    intro a b he
    apply hphi
    exact neg_injective he
  have hb := bounded_integer_sum_le ((Finset.univ : Finset (Fin N)) ×ˢ (Finset.univ : Finset V))
    (fun ri => -((N : ℤ) * site ri.2 + ((ri.1.val + 1 : ℕ) : ℤ))) hneg T (truncatedPaddingWeight Q L)
    (truncatedPaddingWeight_nonneg Q L)
  simpa only [Finset.sum_product, Int.cast_neg] using hb

#print axioms source_test_energy_to_interval
#print axioms target_test_energy_to_interval

end ReflectedLiouville
