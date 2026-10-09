import ReflectedLiouville.BinGeometry
import ReflectedLiouville.RawDilation
import ReflectedLiouville.CenterDeletionCost

set_option autoImplicit false
open scoped BigOperators Classical
open OAI.TwoPointCorrelations

namespace ReflectedLiouville

noncomputable def retainedPairMass (I : Finset (ℕ × ℕ)) : ℝ :=
  ∑ dq ∈ I, actualPaddingCoefficient dq.2 / ((dq.1 * dq.2 : ℕ) : ℝ)

noncomputable def reflectionPairBin (η : ℝ) (dq : ℕ × ℕ) : ℤ :=
  paddingBin η 0 (Real.log ((dq.1 * dq.2 : ℕ) : ℝ))

noncomputable def reflectionBinCutoff (N : ℕ) (η : ℝ) (j : ℤ) : ℝ :=
  (N : ℝ) * Real.exp ((j : ℝ) * η)

/-- Pair-first finite sum for the paper's raw R_j, with the real denominator. -/
noncomputable def rawBinForm (I : Finset (ℕ × ℕ)) (N : ℕ) (η : ℝ) (j : ℤ) : ℝ :=
  ∑ dq ∈ I.filter (fun dq => reflectionPairBin η dq = j),
    actualPaddingCoefficient dq.2 *
      (dilatedReflectedSum N (dq.1 * dq.2) ⌊reflectionBinCutoff N η j⌋₊ / reflectionBinCutoff N η j)

noncomputable def rawPairTotal (I : Finset (ℕ × ℕ)) (N : ℕ) (η : ℝ) : ℝ :=
  ∑ dq ∈ I, actualPaddingCoefficient dq.2 *
    (dilatedReflectedSum N (dq.1 * dq.2) ⌊reflectionBinCutoff N η (reflectionPairBin η dq)⌋₊ /
      reflectionBinCutoff N η (reflectionPairBin η dq))

lemma raw_bin_forms_sum (I : Finset (ℕ × ℕ)) (bins : Finset ℤ) (N : ℕ) (η : ℝ)
    (hcover : ∀ dq ∈ I, reflectionPairBin η dq ∈ bins) :
    (∑ j ∈ bins, rawBinForm I N η j) = rawPairTotal I N η := by
  unfold rawBinForm rawPairTotal
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro dq hdq
  simp only [Finset.sum_ite_eq, hcover dq hdq, ite_true]

lemma retainedPairMass_nonneg (I : Finset (ℕ × ℕ)) : 0 ≤ retainedPairMass I := by
  unfold retainedPairMass
  exact Finset.sum_nonneg (fun dq _ => div_nonneg (actualPaddingCoefficient_nonneg dq.2) (Nat.cast_nonneg _))

/-- The paper's complete dilation step for the actual bin chosen by each
    numerical pair. No assumption that a real cutoff is an integer is used. -/
theorem raw_bin_dilation_bound (I : Finset (ℕ × ℕ)) (N : ℕ) (η : ℝ)
    (hN : 0 < N) (hη : 0 < η) (hηhalf : η ≤ 1 / 2)
    (hpositive : ∀ dq ∈ I, 0 < dq.1 * dq.2) :
    |rawPairTotal I N η - retainedPairMass I * (reflectedSum N / N)| ≤
      (4 * η + 2 / N) * retainedPairMass I := by
  have hb := raw_sum_dilation_bound I N (fun dq => dq.1 * dq.2)
    (fun dq => reflectionBinCutoff N η (reflectionPairBin η dq))
    (fun dq => actualPaddingCoefficient dq.2) η hN hη.le hηhalf hpositive
    (fun dq _ => actualPaddingCoefficient_nonneg dq.2)
    (fun dq hdq => (actual_pair_bin_cutoff_bounds N (dq.1 * dq.2) (hpositive dq hdq) η hη).1)
    (fun dq hdq => (actual_pair_bin_cutoff_bounds N (dq.1 * dq.2) (hpositive dq hdq) η hη).2)
  exact hb

lemma retainedPairMass_le_product_mass (I : Finset (ℕ × ℕ)) (D Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) (hI : I ⊆ D ×ˢ retainedPrimeDivisors Q) :
    retainedPairMass I ≤ paddingTiltNormalizer Q * (∑ d ∈ D, 1 / (d : ℝ)) := by
  unfold retainedPairMass
  calc
    _ ≤ ∑ dq ∈ D ×ˢ retainedPrimeDivisors Q,
        actualPaddingCoefficient dq.2 / ((dq.1 * dq.2 : ℕ) : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hI
      intro dq hdq hnot
      exact div_nonneg (actualPaddingCoefficient_nonneg _) (Nat.cast_nonneg _)
    _ = ∑ d ∈ D, (1 / (d : ℝ)) * paddingTiltNormalizer Q := by
      rw [Finset.sum_product]
      apply Finset.sum_congr rfl
      intro d hd
      rw [paddingTiltNormalizer_eq_divisor_sum Q hQ, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      simp only [actualPaddingCoefficient, Nat.cast_mul]
      ring
    _ = _ := by rw [← Finset.sum_mul]; ring

lemma actual_pair_mass_eq_bin_mass (N : ℕ) [NeZero N] (W δ L η : ℝ)
    (hL : 1 ≤ L) (hW : 0 ≤ W) (hη : 0 < η) :
    let data := reflectionPrimeFamily N W δ L η hL hW
    let P := centeredPrimeBands N.primeFactors (L ^ (1 - δ)) W (reflectionBandCount W δ L)
    retainedPairMass data.pairs = totalPaddingBinMass (primeTupleDivisors P) data.Q L η := by
  dsimp only
  let P := centeredPrimeBands N.primeFactors (L ^ (1 - δ)) W (reflectionBandCount W δ L)
  let Q := paddingPrimeSupply N.primeFactors L
  change retainedPairMass (primeFamilyPairs P Q ⌊100 * Real.log L⌋₊ (PaddingPairEligible L η)) =
    totalPaddingBinMass (primeTupleDivisors P) Q L η
  rw [totalPaddingBinMass_eq _ _ _ _ hη]
  unfold retainedPairMass primeFamilyPairs paddingPairHarmonicMass
  rw [Finset.sum_filter, Finset.product_eq_sprod, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro d hd
  unfold boundedPaddingDivisors
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases he : PaddingPairEligible L η d q
  · have hcap : q.primeFactors.card ≤ ⌊100 * Real.log L⌋₊ := Nat.le_floor he.1
    simp only [he, hcap, ite_true, actualPaddingCoefficient]
  · simp only [he, ite_false, ite_self]

#print axioms raw_bin_dilation_bound
#print axioms actual_pair_mass_eq_bin_mass

end ReflectedLiouville
