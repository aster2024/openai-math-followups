import ReflectedLiouville.ReflectionPoolBounds
import OAI.NumberTheory.TwoPoint.Bounds.DegreeCostResidue

set_option autoImplicit false
open scoped BigOperators Classical
open OAI.TwoPointCorrelations

namespace ReflectedLiouville

lemma reciprocal_padding_subset_mass (Q D : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (hD : D ⊆ retainedPrimeDivisors Q) :
    (∑ q ∈ D, actualPaddingCoefficient q / (q : ℝ)) ≤ paddingTiltNormalizer Q := by
  rw [paddingTiltNormalizer_eq_divisor_sum Q hQ]
  apply Finset.sum_le_sum_of_subset_of_nonneg hD
  intro q hq hnot
  exact div_nonneg (actualPaddingCoefficient_nonneg q) (Nat.cast_nonneg q)

/-- Positive center-degree deletion atoms, each at its own offset, are summed
    only after their individual model estimates. -/
theorem center_degree_deletion_cost {h J M B : ℕ}
    (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (W : ℝ) (hW : 10 ≤ W)
    (hmass : (∑ p ∈ data.P, 1 / (p : ℝ)) ≤ 2 * W * J)
    (T : Finset ℕ) (padding : ℕ → Finset ℕ)
    (hT : ∀ d ∈ T, Squarefree d ∧ d.primeFactors.card = J ∧ d.primeFactors ⊆ data.P)
    (hpadding : ∀ d ∈ T, padding d ⊆ retainedPrimeDivisors data.Q)
    (site : ℕ → ℕ → ℤ) :
    (∑ d ∈ T, ∑ q ∈ padding d, (data.residueLaw B hB).average (fun x =>
      actualPaddingCoefficient q * positivePrimeWeight d.primeFactors (data.residueOrigin x + site d q) *
        if (q : ℤ) ∣ data.residueOrigin x + site d q ∧
          6 * W * J < (actualPaddingDegree data.P (data.residueOrigin x + site d q) : ℝ)
        then 1 else 0)) ≤
      paddingTiltNormalizer data.Q * (∑ d ∈ T, 1 / (d : ℝ)) * (2 : ℝ) ^ J * Real.exp (-2 * W * J) := by
  have hpoint (d : ℕ) (hd : d ∈ T) (q : ℕ) (hq : q ∈ padding d) :=
    data.positive_divisor_degree_cost hB d.primeFactors (hT d hd).2.2 q (hpadding d hd hq) W hW
      (by simpa only [(hT d hd).2.1] using hmass) (site d q)
  have hrow (d : ℕ) (hd : d ∈ T) :
      (∑ q ∈ padding d, (data.residueLaw B hB).average (fun x =>
        actualPaddingCoefficient q * positivePrimeWeight d.primeFactors (data.residueOrigin x + site d q) *
          if (q : ℤ) ∣ data.residueOrigin x + site d q ∧
            6 * W * J < (actualPaddingDegree data.P (data.residueOrigin x + site d q) : ℝ)
          then 1 else 0)) ≤
        paddingTiltNormalizer data.Q * ((2 : ℝ) ^ J / d) * Real.exp (-2 * W * J) := by
    have hp (q : ℕ) (hq : q ∈ padding d) := hpoint d hd q hq
    have hp' (q : ℕ) (hq : q ∈ padding d) :
        (data.residueLaw B hB).average (fun x =>
          actualPaddingCoefficient q * positivePrimeWeight d.primeFactors (data.residueOrigin x + site d q) *
            if (q : ℤ) ∣ data.residueOrigin x + site d q ∧
              6 * W * J < (actualPaddingDegree data.P (data.residueOrigin x + site d q) : ℝ)
            then 1 else 0) ≤
          (actualPaddingCoefficient q / q) * ((2 : ℝ) ^ J / d) * Real.exp (-2 * W * J) := by
      simpa only [positivePrimeNormalizer_squarefree d (hT d hd).1, (hT d hd).2.1] using hp q hq
    calc
      _ ≤ ∑ q ∈ padding d, (actualPaddingCoefficient q / q) * ((2 : ℝ) ^ J / d) * Real.exp (-2 * W * J) :=
        Finset.sum_le_sum hp'
      _ = (∑ q ∈ padding d, actualPaddingCoefficient q / q) * ((2 : ℝ) ^ J / d) * Real.exp (-2 * W * J) := by
        rw [Finset.sum_mul, Finset.sum_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (reciprocal_padding_subset_mass data.Q (padding d) data.primeQ (hpadding d hd))
          (by positivity)) (Real.exp_pos _).le
  apply (Finset.sum_le_sum hrow).trans_eq
  rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d hd
  ring

#print axioms center_degree_deletion_cost

end ReflectedLiouville
