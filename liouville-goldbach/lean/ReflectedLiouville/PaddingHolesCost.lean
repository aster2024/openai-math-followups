import ReflectedLiouville.ReducedPaddingCost
import ReflectedLiouville.ReflectionPrimeGeometry

set_option autoImplicit false
open Filter
open scoped BigOperators Classical
open OAI.TwoPointCorrelations

namespace ReflectedLiouville

lemma padding_pool_removed_subset (E : Finset ℕ) (L : ℝ) :
    paddingPrimeSupply ∅ L \ paddingPrimeSupply E L ⊆ E := by
  intro p hp
  simp only [paddingPrimeSupply, deletedModFivePrimes, Finset.sdiff_empty] at hp
  obtain ⟨hfull, hnot⟩ := Finset.mem_sdiff.mp hp
  by_contra hpE
  exact hnot (Finset.mem_sdiff.mpr ⟨hfull, hpE⟩)

/-- Full Lemma paddingholes at the positive single-tuple envelope, uniformly
    in the changing N, bin translation, retained divisor subset and site. -/
theorem padding_holes_cost (a : ℝ) (ha : 1 ≤ a) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (N : ℕ) [NeZero N], Real.exp 2 ≤ (N : ℝ) → Real.log (N : ℝ) ≤ L ^ a →
        ∀ (h J M B : ℕ) (data : ProhibitedPrimeFamily h J M),
          data.Q = paddingPrimeSupply N.primeFactors L →
          ∀ (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
            (D S : Finset ℕ) (bins : Finset ℤ) (η c K : ℝ) (site : ℤ),
            D ⊆ retainedPrimeDivisors data.Q → S ⊆ data.P →
            0 < η → η ≤ 1 → 0 < K →
            (data.residueLaw B hB).average (fun x =>
              positivePrimeWeight S (data.residueOrigin x + site) *
                paddingRejectedMass data.Q D bins η c L K (data.residueOrigin x + site)) /
                  paddingTiltNormalizer data.Q ≤
              positivePrimeNormalizer S * (C * (Real.log L) ^ (10 : ℕ) / K + L ^ (-90 : ℝ)) := by
  obtain ⟨C, hC, hb⟩ := eventually_reduced_boolean_padding_cost a ha
  refine ⟨C, hC, ?_⟩
  filter_upwards [hb] with L hL
  intro N inst hN hNlog h J M B data hQ hB D S bins η c K site hD hSP hη hη₁ hK
  have hsubset : data.Q ⊆ paddingPrimeSupply ∅ L := by
    rw [hQ]
    exact paddingPrimeSupply_subset_empty _ _
  have hremoved : paddingPrimeSupply ∅ L \ data.Q ⊆ N.primeFactors := by
    rw [hQ]
    exact padding_pool_removed_subset _ _
  have hc := hL N hN hNlog data.Q hsubset hremoved D bins η c K hD hη hη₁ hK
  have hnative : (data.residueLaw B hB).average (fun x =>
      paddingRejectedMass data.Q D bins η c L K (data.residueOrigin x + site)) /
        paddingTiltNormalizer data.Q ≤ C * (Real.log L) ^ (10 : ℕ) / K + L ^ (-90 : ℝ) := by
    rw [residue_padding_cost_eq_original data hB D hD bins η c L K site]
    exact hc
  have heq := data.positive_prime_padding_factor hB S hSP site
    (paddingRejectedMass data.Q D bins η c L K)
    (paddingRejectedMass_residue_congr data.Q data.primeQ D hD bins η c L K)
  rw [heq]
  have hpos : 0 ≤ positivePrimeNormalizer S := by unfold positivePrimeNormalizer; positivity
  have hc' := mul_le_mul_of_nonneg_left hnative hpos
  convert hc' using 1 <;> ring

/-- Summation preserves the exact tuple harmonic mass. This is the displayed
    SV_* normalization of the paper's paddingholes estimate. -/
theorem padding_holes_tuple_sum (a : ℝ) (ha : 1 ≤ a) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (N : ℕ) [NeZero N], Real.exp 2 ≤ (N : ℝ) → Real.log (N : ℝ) ≤ L ^ a →
        ∀ (h J M B : ℕ) (data : ProhibitedPrimeFamily h J M),
          data.Q = paddingPrimeSupply N.primeFactors L →
          ∀ (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
            (T : Finset ℕ) (D : ℕ → Finset ℕ) (bins : ℕ → Finset ℤ)
            (η K : ℝ) (c : ℕ → ℝ) (site : ℕ → ℤ),
            (∀ d ∈ T, Squarefree d ∧ d.primeFactors.card = J ∧ d.primeFactors ⊆ data.P) →
            (∀ d ∈ T, D d ⊆ retainedPrimeDivisors data.Q) →
            0 < η → η ≤ 1 → 0 < K →
            (∑ d ∈ T, (data.residueLaw B hB).average (fun x =>
              positivePrimeWeight d.primeFactors (data.residueOrigin x + site d) *
                paddingRejectedMass data.Q (D d) (bins d) η (c d) L K (data.residueOrigin x + site d))) ≤
              paddingTiltNormalizer data.Q * (∑ d ∈ T, 1 / (d : ℝ)) * (2 : ℝ) ^ J *
                (C * (Real.log L) ^ (10 : ℕ) / K + L ^ (-90 : ℝ)) := by
  obtain ⟨C, hC, hb⟩ := padding_holes_cost a ha
  refine ⟨C, hC, ?_⟩
  filter_upwards [hb] with L hL
  intro N inst hN hNlog h J M B data hQ hB T D bins η K c site hT hD hη hη₁ hK
  have hpoint (d : ℕ) (hd : d ∈ T) :
      (data.residueLaw B hB).average (fun x => positivePrimeWeight d.primeFactors (data.residueOrigin x + site d) *
        paddingRejectedMass data.Q (D d) (bins d) η (c d) L K (data.residueOrigin x + site d)) ≤
      paddingTiltNormalizer data.Q * ((2 : ℝ) ^ J / d) *
        (C * (Real.log L) ^ (10 : ℕ) / K + L ^ (-90 : ℝ)) := by
    have hc := hL N hN hNlog h J M B data hQ hB (D d) d.primeFactors (bins d) η (c d) K (site d)
      (hD d hd) (hT d hd).2.2 hη hη₁ hK
    rw [positivePrimeNormalizer_squarefree d (hT d hd).1, (hT d hd).2.1] at hc
    have hc' := (div_le_iff₀ (paddingTiltNormalizer_pos data.Q)).mp hc
    convert hc' using 1 <;> ring
  apply (Finset.sum_le_sum hpoint).trans_eq
  rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d hd
  ring

#print axioms padding_holes_cost
#print axioms padding_holes_tuple_sum

end ReflectedLiouville
