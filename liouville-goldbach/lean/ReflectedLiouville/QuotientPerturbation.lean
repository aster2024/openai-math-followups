import ReflectedLiouville.QuotientWindowSquare
import OAI.NumberTheory.TwoPoint.Fourier.MajorArcPerturbation

set_option autoImplicit false
open scoped BigOperators
open OAI.TwoPointCorrelations

namespace ReflectedLiouville

noncomputable def quotientWindowFrequency (N r v h : ℕ) (θ : ℝ) : ℂ :=
  ∑ m ∈ Finset.Icc (v + 1) (v + h), liouville (N * m + r) * additiveCharacter θ m

lemma quotientWindowFrequency_eq_short (N r v h : ℕ) (θ : ℝ) :
    quotientWindowFrequency N r v h θ =
      shortExponentialSum (fun m => liouville (N * m + r)) h θ (v : ℝ) := by
  rw [shortExponentialSum_at_nat]
  rfl

/-- The library's proved finite Abel perturbation applies directly in quotient
    coordinates; all shorter prefixes remain visible. -/
theorem quotient_frequency_perturbation (N r v h : ℕ) (α β : ℝ) :
    ‖quotientWindowFrequency N r v h (α + β)‖ ≤
      ‖quotientWindowFrequency N r v h α‖ + 2 * Real.pi * |β| *
        (∑ j ∈ Finset.range (h - 1), ‖quotientWindowFrequency N r v (j + 1) α‖) := by
  simp only [quotientWindowFrequency_eq_short]
  exact major_arc_frequency_perturbation (fun m => liouville (N * m + r)) h v α β

theorem quotient_frequency_perturbation_sum (N K h : ℕ) (α β : ℝ) :
    (∑ v ∈ Finset.range K, ∑ r : Fin N, ‖quotientWindowFrequency N (r.val + 1) v h (α + β)‖) ≤
      (∑ v ∈ Finset.range K, ∑ r : Fin N, ‖quotientWindowFrequency N (r.val + 1) v h α‖) +
      2 * Real.pi * |β| *
        (∑ j ∈ Finset.range (h - 1), ∑ v ∈ Finset.range K, ∑ r : Fin N,
          ‖quotientWindowFrequency N (r.val + 1) v (j + 1) α‖) := by
  have hbound : (∑ v ∈ Finset.range K, ∑ r : Fin N, ‖quotientWindowFrequency N (r.val + 1) v h (α + β)‖) ≤
      ∑ v ∈ Finset.range K, ∑ r : Fin N,
        (‖quotientWindowFrequency N (r.val + 1) v h α‖ + 2 * Real.pi * |β| *
          (∑ j ∈ Finset.range (h - 1), ‖quotientWindowFrequency N (r.val + 1) v (j + 1) α‖)) := by
    apply Finset.sum_le_sum
    intro v hv
    exact Finset.sum_le_sum (fun r _ => quotient_frequency_perturbation N (r.val + 1) v h α β)
  apply hbound.trans_eq
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  congr 1
  congr 1
  conv_lhs =>
    arg 2
    ext v
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]

#print axioms quotient_frequency_perturbation_sum

end ReflectedLiouville
