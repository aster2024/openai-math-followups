import ReflectedLiouville.PaddingRestriction
import ReflectedLiouville.NormalizedConditioning

set_option autoImplicit false
open scoped BigOperators Classical
open OAI.TwoPointCorrelations

namespace ReflectedLiouville

noncomputable def activePaddingDensity (D A : Finset ℕ) (η c : ℝ) (j : ℤ) : ℝ :=
  (∑ q ∈ D, if q.primeFactors ⊆ A ∧ actualPaddingBin η c j q then actualPaddingCoefficient q else 0) /
    (5 : ℝ) ^ A.card

noncomputable def activePaddingRejected (D : Finset ℕ) (bins : Finset ℤ)
    (η c L K : ℝ) (A : Finset ℕ) : ℝ :=
  (5 : ℝ) ^ A.card * ∑ j ∈ bins,
    if ¬(activePaddingDensity D A η c j ≤ K / L ∧ (A.card : ℝ) ≤ 400 * Real.log L)
    then activePaddingDensity D A η c j else 0

lemma activePaddingDensity_nonneg (D A : Finset ℕ) (η c : ℝ) (j : ℤ) :
    0 ≤ activePaddingDensity D A η c j := by
  unfold activePaddingDensity
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro q hq
    split_ifs
    · exact actualPaddingCoefficient_nonneg q
    · exact le_rfl
  · positivity

lemma activePaddingRejected_nonneg (D : Finset ℕ) (bins : Finset ℤ)
    (η c L K : ℝ) (A : Finset ℕ) : 0 ≤ activePaddingRejected D bins η c L K A := by
  unfold activePaddingRejected
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro j hj
  split_ifs
  all_goals first | exact activePaddingDensity_nonneg _ _ _ _ _ | exact le_rfl

lemma actual_density_eq_active (Q D : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (hD : D ⊆ retainedPrimeDivisors Q) (n : ℤ) (η c : ℝ) (j : ℤ) :
    paddingDensity D actualPaddingCoefficient (actualPaddingBin η c j) (actualPaddingVertex Q) n =
      activePaddingDensity D (paddingAvailablePrimes Q (fun p => decide ((p.val : ℤ) ∣ n))) η c j := by
  unfold paddingDensity activePaddingDensity
  rw [actualPaddingVertex_sq, actualPaddingWeight, actualPaddingDegree_eq_available]
  congr 1
  apply Finset.sum_congr rfl
  intro q hq
  simp only [padding_literal_support_iff_dvd Q hQ n q (hD hq), and_comm]

/-- The literal graph deletion is a function solely of the active prime set;
    the divisor subset and bin set are unchanged by changing the ambient pool. -/
theorem paddingRejectedMass_eq_active (Q D : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (hD : D ⊆ retainedPrimeDivisors Q) (n : ℤ) (bins : Finset ℤ) (η c L K : ℝ) :
    paddingRejectedMass Q D bins η c L K n =
      activePaddingRejected D bins η c L K
        (paddingAvailablePrimes Q (fun p => decide ((p.val : ℤ) ∣ n))) := by
  unfold paddingRejectedMass activePaddingRejected
  rw [actualPaddingVertex_sq, actualPaddingWeight, actualPaddingDegree_eq_available]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hrho := actual_density_eq_active Q D hQ hD n η c j
  have hkeep : integerEdgeKeep D actualPaddingCoefficient (actualPaddingBin η c j)
      (actualPaddingVertex Q) L K (actualPaddingDegreeCut Q L) n ↔
      activePaddingDensity D (paddingAvailablePrimes Q (fun p => decide ((p.val : ℤ) ∣ n))) η c j ≤ K / L ∧
        ((paddingAvailablePrimes Q (fun p => decide ((p.val : ℤ) ∣ n))).card : ℝ) ≤ 400 * Real.log L := by
    unfold integerEdgeKeep actualPaddingDegreeCut
    rw [hrho, actualPaddingDegree_eq_available]
  rw [propext hkeep, hrho]
  split_ifs <;> rfl

#print axioms paddingRejectedMass_eq_active

end ReflectedLiouville
