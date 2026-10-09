import ReflectedLiouville.ExplicitPositiveCosts
import OAI.NumberTheory.TwoPoint.Bounds.PaddingDeletionComparison

set_option autoImplicit false
set_option maxHeartbeats 1200000
open OAI.TwoPointCorrelations Finset Filter
open scoped Classical
namespace ReflectedLiouville

theorem explicit_padding_atom_comparison :
    ∀ᶠ L : ℝ in atTop,
      ∀ (h J M B : ℕ) (data : ProhibitedPrimeFamily h J M)
        (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B),
      (data.P ∪ data.Q).Nonempty → (B : ℝ) ≤ Real.exp L →
      ∀ (S : Finset ℕ), S ⊆ data.P ∪ data.Q → (S.card : ℝ) ≤ L ^ 2 →
      ∀ (q : ℕ), q ∈ retainedPrimeDivisors data.Q →
      (q.primeFactors.card : ℝ) ≤ 100 * Real.log L →
      ∀ (D : Finset ℕ), D ⊆ retainedPrimeDivisors data.Q →
      ∀ (eligible : ℕ → Prop) (K : ℝ) (site : ℤ) (a N : ℕ),
      Real.exp (L ^ (289578 : ℕ) / 2) ≤ (N : ℝ) →
      |uniformAverage (fun x : Fin N =>
          paddingRejectionAtom data.Q S D eligible L K q ((a + x.val : ℤ) + site)) -
        (data.residueLaw B hB).average (fun x =>
          paddingRejectionAtom data.Q S D eligible L K q (data.residueOrigin x + site))| ≤
            2 * Real.exp (-(L ^ 9)) := by
  have hd := explicit_degree_cost_comparison
  have hs := explicit_density_cost_comparison
  filter_upwards [hd, hs, eventually_ge_atTop (1 : ℝ)] with L hd hs hL
  intro h J M B data hB hpool hBL S hS hSL q hq hqdegree D hD eligible K site a N hN
  have hN₁ : Real.exp (L ^ (144789 : ℕ) / 2) ≤ (N : ℝ) :=
    (Real.exp_le_exp.mpr (div_le_div_of_nonneg_right
      (pow_le_pow_right₀ hL (by norm_num : (144789 : ℕ) ≤ 289578)) (by norm_num))).trans hN
  have hN₂ := hN₁
  by_cases he : eligible q
  · let H := fun n : ℤ => actualPaddingCoefficient q * positivePrimeWeight S n *
        if (q : ℤ) ∣ n ∧ 400 * Real.log L < (actualPaddingDegree data.Q n : ℝ) then 1 else 0
    let G := fun n : ℤ => actualPaddingCoefficient q * positivePrimeWeight S n *
        if (q : ℤ) ∣ n ∧ actualPaddingDegreeCut data.Q L n ∧
          K / L < paddingDensity D actualPaddingCoefficient eligible (actualPaddingVertex data.Q) n
          then 1 else 0
    have hlog : 0 ≤ 400 * Real.log L := mul_nonneg (by norm_num) (Real.log_nonneg hL)
    have hH := hd h J M B data hB hpool hBL S data.Q hS subset_union_right hSL
      q hq hqdegree (400 * Real.log L) hlog le_rfl site a N hN₁
    have hG := hs h J M B data hB hpool hBL S hS hSL q hq hqdegree D hD eligible K site a N hN₂
    have hsplit (n : ℤ) : paddingRejectionAtom data.Q S D eligible L K q n = H n + G n := by
      simp only [paddingRejectionAtom, he, ite_true, padding_rejection_failure_split, mul_add, H, G]
    simp_rw [hsplit]
    have hu : uniformAverage (fun x : Fin N => H ((a + x.val : ℤ) + site) +
        G ((a + x.val : ℤ) + site)) =
        uniformAverage (fun x : Fin N => H ((a + x.val : ℤ) + site)) +
        uniformAverage (fun x : Fin N => G ((a + x.val : ℤ) + site)) := by
      simp only [uniformAverage, sum_add_distrib, add_div]
    rw [hu, (data.residueLaw B hB).average_add]
    calc
      _ = |(uniformAverage (fun x : Fin N => H ((a + x.val : ℤ) + site)) -
          (data.residueLaw B hB).average (fun x => H (data.residueOrigin x + site))) +
          (uniformAverage (fun x : Fin N => G ((a + x.val : ℤ) + site)) -
          (data.residueLaw B hB).average (fun x => G (data.residueOrigin x + site)))| := by
            congr 1
            ring
      _ ≤ _ := (abs_add_le _ _).trans (show _ ≤ 2 * Real.exp (-(L ^ 9)) by linarith [hH, hG])
  · simp only [paddingRejectionAtom, he, ite_false, uniformAverage, sum_const_zero,
      zero_div, (data.residueLaw B hB).average_const, sub_self, abs_zero]
    positivity

#print axioms explicit_padding_atom_comparison
end ReflectedLiouville
