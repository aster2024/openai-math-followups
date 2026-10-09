import ReflectedLiouville.IndependentConditioning
import ReflectedLiouville.PaddingHoleProduct
import OAI.NumberTheory.TwoPoint.Bounds.PaddingCutCost

set_option autoImplicit false
open scoped BigOperators
open OAI.TwoPointCorrelations

namespace ReflectedLiouville

lemma padding_active_primes_of_removed_inactive (Q R : Finset ℕ) (hQR : Q ⊆ R)
    (n : ℤ) (hinactive : ∀ p ∈ R, p ∉ Q → ¬ (p : ℤ) ∣ n) :
    R.filter (fun p : ℕ => (p : ℤ) ∣ n) = Q.filter (fun p : ℕ => (p : ℤ) ∣ n) := by
  classical
  ext p
  simp only [Finset.mem_filter]
  constructor
  · intro h
    have hpQ : p ∈ Q := by
      by_contra hnot
      exact hinactive p h.1 hnot h.2
    exact ⟨hpQ, h.2⟩
  · intro h
    exact ⟨hQR h.1, h.2⟩

lemma padding_degree_of_removed_inactive (Q R : Finset ℕ) (hQR : Q ⊆ R)
    (n : ℤ) (hinactive : ∀ p ∈ R, p ∉ Q → ¬ (p : ℤ) ∣ n) :
    actualPaddingDegree R n = actualPaddingDegree Q n := by
  unfold actualPaddingDegree
  rw [padding_active_primes_of_removed_inactive Q R hQR n hinactive]

lemma padding_vertex_of_removed_inactive (Q R : Finset ℕ) (hQR : Q ⊆ R)
    (n : ℤ) (hinactive : ∀ p ∈ R, p ∉ Q → ¬ (p : ℤ) ∣ n) :
    actualPaddingVertex R n = actualPaddingVertex Q n := by
  unfold actualPaddingVertex actualPaddingWeight
  rw [padding_degree_of_removed_inactive Q R hQR n hinactive]

/-- Exactly the same divisor subset and bins are used on the two sides.
    Only the pool weight and degree change, and agree under conditioning. -/
lemma padding_rejected_mass_of_removed_inactive (Q R D : Finset ℕ)
    (hQR : Q ⊆ R) (bins : Finset ℤ) (η c L K : ℝ) (n : ℤ)
    (hinactive : ∀ p ∈ R, p ∉ Q → ¬ (p : ℤ) ∣ n) :
    paddingRejectedMass R D bins η c L K n = paddingRejectedMass Q D bins η c L K n := by
  have hg := padding_vertex_of_removed_inactive Q R hQR n hinactive
  have hc : actualPaddingDegreeCut R L n ↔ actualPaddingDegreeCut Q L n := by
    unfold actualPaddingDegreeCut
    rw [padding_degree_of_removed_inactive Q R hQR n hinactive]
  unfold paddingRejectedMass
  rw [hg]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hrho : paddingDensity D actualPaddingCoefficient (actualPaddingBin η c j)
      (actualPaddingVertex R) n =
      paddingDensity D actualPaddingCoefficient (actualPaddingBin η c j)
        (actualPaddingVertex Q) n := by
    unfold paddingDensity
    rw [hg]
  have hkeep : integerEdgeKeep D actualPaddingCoefficient (actualPaddingBin η c j)
      (actualPaddingVertex R) L K (actualPaddingDegreeCut R L) n ↔
      integerEdgeKeep D actualPaddingCoefficient (actualPaddingBin η c j)
        (actualPaddingVertex Q) L K (actualPaddingDegreeCut Q L) n := by
    unfold integerEdgeKeep
    rw [hrho, hc]
  rw [propext hkeep, hrho]

#print axioms padding_rejected_mass_of_removed_inactive

end ReflectedLiouville
