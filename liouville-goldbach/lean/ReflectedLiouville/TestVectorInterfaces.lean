import ReflectedLiouville.ProjectedSparseTesting

set_option autoImplicit false
open scoped BigOperators Classical
open OAI.TwoPointCorrelations

namespace ReflectedLiouville

noncomputable def unweightedSourceTest (T : ℝ) (n : ℤ) : ℂ :=
  if 0 < n ∧ (n : ℝ) ≤ T then (liouvilleAtInteger n : ℂ) else 0

noncomputable def unweightedTargetTest (T : ℝ) (n : ℤ) : ℂ := unweightedSourceTest T (-n)

lemma unweightedSourceTest_one_bounded (T : ℝ) (n : ℤ) : ‖unweightedSourceTest T n‖ ≤ 1 := by
  unfold unweightedSourceTest
  split_ifs
  · rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_liouvilleAtInteger_le n
  · norm_num

lemma unweightedTargetTest_one_bounded (T : ℝ) (n : ℤ) : ‖unweightedTargetTest T n‖ ≤ 1 :=
  unweightedSourceTest_one_bounded T (-n)

lemma sourceTestVector_eq_padding {V : Type*} [Fintype V]
    (Q : Finset ℕ) (T L : ℝ) (physical : V → ℤ) :
    sourceTestVector Q T L physical = paddingTestVector Q L physical (unweightedSourceTest T) := by
  ext i
  change (sourceTestValue Q T L (physical i) : ℂ) =
    if actualPaddingDegreeCut Q L (physical i) then
      (actualPaddingVertex Q (physical i) : ℂ) * unweightedSourceTest T (physical i) else 0
  by_cases h0 : 0 < physical i <;> by_cases hu : (physical i : ℝ) ≤ T <;>
    by_cases hc : actualPaddingDegreeCut Q L (physical i) <;>
    simp [sourceTestValue, unweightedSourceTest, h0, hu, hc, Complex.ofReal_mul, mul_comm]

lemma targetTestVector_eq_padding {V : Type*} [Fintype V]
    (Q : Finset ℕ) (T L : ℝ) (physical : V → ℤ) :
    targetTestVector Q T L physical = paddingTestVector Q L physical (unweightedTargetTest T) := by
  ext i
  change (targetTestValue Q T L (physical i) : ℂ) =
    if actualPaddingDegreeCut Q L (physical i) then
      (actualPaddingVertex Q (physical i) : ℂ) * unweightedTargetTest T (physical i) else 0
  by_cases h0 : 0 < -physical i <;> by_cases hu : ((-physical i : ℤ) : ℝ) ≤ T <;>
    by_cases hc : actualPaddingDegreeCut Q L (physical i) <;>
    simp [targetTestValue, sourceTestValue, unweightedTargetTest, unweightedSourceTest,
      actualPaddingVertex_neg, actualPaddingDegreeCut_neg, h0, hu, hc, Complex.ofReal_mul, mul_comm] <;>
      split_ifs <;> simp only [Complex.ofReal_mul, Complex.ofReal_zero]

#print axioms sourceTestVector_eq_padding
#print axioms targetTestVector_eq_padding

end ReflectedLiouville
