import ReflectedLiouville.ReflectedTestVectors
import ReflectedLiouville.FourierWindowReduction
import OAI.NumberTheory.TwoPoint.Bounds.ActualPaddingIntegerBounds

set_option autoImplicit false
open Filter
open scoped BigOperators Classical
open OAI.TwoPointCorrelations

namespace ReflectedLiouville

/-- Real-cutoff form of the proved truncated-padding-weight comparison. -/
theorem initial_truncated_padding_weight_bound :
    ∃ A : ℕ, 1000 ≤ A ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (Q : Finset ℕ), (∀ p ∈ Q, p.Prime) → (∀ p ∈ Q, (p : ℝ) ≤ Real.exp L) →
        ∀ (N : ℕ) (T : ℝ), 0 < N → (N : ℝ) ≤ T → Real.exp (L ^ A / 2) ≤ (N : ℝ) →
          (∑ n ∈ Finset.Icc 1 ⌊T⌋₊, truncatedPaddingWeight Q L (n : ℤ)) ≤
            2 * paddingTiltNormalizer Q * T := by
  obtain ⟨A, hA, hb⟩ := bravermanDepth22Input.eventually_actual_padding_weight
  refine ⟨A, hA, ?_⟩
  filter_upwards [hb] with L hbound
  intro Q hQ hupper N T hN hNT hlength
  let U := ⌊T⌋₊
  have hNU : N ≤ U := Nat.le_floor hNT
  have hUpos : 0 < U := hN.trans_le hNU
  have hUr : (0 : ℝ) < U := by exact_mod_cast hUpos
  have hUl : Real.exp (L ^ A / 2) ≤ (U : ℝ) := hlength.trans (by exact_mod_cast hNU)
  have hc := (hbound Q hQ hupper 0 1 U hUl).2
  have hmean : (∑ r : Fin U, truncatedPaddingWeight Q L (((r.val + 1 : ℕ) : ℤ))) / (U : ℝ) ≤
      2 * paddingTiltNormalizer Q := by
    simpa only [uniformAverage, Fintype.card_fin, truncatedPaddingWeight, add_zero, Nat.add_comm 1] using hc
  have hsum := (div_le_iff₀ hUr).mp hmean
  have heq := sum_fin_shift_eq_Icc U (fun n => truncatedPaddingWeight Q L (n : ℤ))
  change (∑ r : Fin U, truncatedPaddingWeight Q L (((r.val + 1 : ℕ) : ℤ))) =
    ∑ n ∈ Finset.Icc 1 U, truncatedPaddingWeight Q L (n : ℤ) at heq
  rw [heq] at hsum
  have hTpos : 0 < T := (by exact_mod_cast hN : (0 : ℝ) < N).trans_le hNT
  apply hsum.trans
  exact mul_le_mul_of_nonneg_left (Nat.floor_le hTpos.le) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (paddingTiltNormalizer_pos Q).le)

/-- The exact averaged test energy needed by the kept-form estimate, with all
    real/floor endpoint effects retained and both signed supports included. -/
theorem reflected_test_energy_bound :
    ∃ A : ℕ, 1000 ≤ A ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (Q : Finset ℕ), (∀ p ∈ Q, p.Prime) → (∀ p ∈ Q, (p : ℝ) ≤ Real.exp L) →
        ∀ (N : ℕ) (T U : ℝ), 0 < N → (N : ℝ) ≤ T → (N : ℝ) ≤ U → U ≤ 3 * T →
          Real.exp (L ^ A / 2) ≤ (N : ℝ) →
          ∀ (V : Type*) [Fintype V] (site : V → ℤ), Function.Injective site →
            (∑ r : Fin N,
              (‖sourceTestVector Q T L (fun i => (N : ℤ) * site i + ((r.val + 1 : ℕ) : ℤ))‖ ^ 2 +
              ‖targetTestVector Q U L (fun i => (N : ℤ) * site i + ((r.val + 1 : ℕ) : ℤ))‖ ^ 2)) ≤
                8 * paddingTiltNormalizer Q * T := by
  obtain ⟨A, hA, hb⟩ := initial_truncated_padding_weight_bound
  refine ⟨A, hA, ?_⟩
  filter_upwards [hb] with L hbound
  intro Q hQ hupper N T U hN hNT hNU hUT hlength V inst site hinj
  have hs := (source_test_energy_to_interval N hN site hinj Q T L).trans
    (hbound Q hQ hupper N T hN hNT hlength)
  have ht := (target_test_energy_to_interval N hN site hinj Q U L).trans
    (hbound Q hQ hupper N U hN hNU hlength)
  rw [Finset.sum_add_distrib]
  have hUbound := mul_le_mul_of_nonneg_left hUT (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (paddingTiltNormalizer_pos Q).le)
  linarith only [hs, ht, hUbound]

#print axioms reflected_test_energy_bound

end ReflectedLiouville
