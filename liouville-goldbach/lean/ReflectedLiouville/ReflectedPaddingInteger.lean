import ReflectedLiouville.PaddingHolesCost
import OAI.NumberTheory.TwoPoint.Bounds.ShiftedPaddingComparison

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Finset Filter
open scoped BigOperators Classical
open OAI.TwoPointCorrelations
namespace ReflectedLiouville

theorem reflected_shifted_padding_deletion
    (hBr : BravermanDepth22Input) :
    ∃ A : ℕ, 1000 ≤ A ∧ ∀ a₀ : ℝ, 1 ≤ a₀ →
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (N₀ : ℕ) [NeZero N₀], Real.exp 2 ≤ (N₀ : ℝ) → Real.log (N₀ : ℝ) ≤ L ^ a₀ →
      ∀ (h J M B : ℕ) (data : ProhibitedPrimeFamily h J M),
      data.Q = paddingPrimeSupply N₀.primeFactors L →
      ∀ (_hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B),
      (data.P ∪ data.Q).Nonempty → (B : ℝ) ≤ Real.exp L →
      ∀ (P : Fin J → Finset ℕ), primeTuplePool P = data.P →
      (∀ j, ∀ p ∈ P j, p.Prime) →
      (∀ j l, l ≠ j → Disjoint (P j) (P l)) → (J : ℝ) ≤ L ^ 2 →
      ∀ (D : Finset ℕ), D ⊆ primeTupleDivisors P →
      ∀ (Q : Finset ℕ), Q ⊆ retainedPrimeDivisors data.Q →
      (∀ q ∈ Q, (q.primeFactors.card : ℝ) ≤ 100 * Real.log L) →
      ∀ (bins : Finset ℤ) (η K : ℝ) (c : ℕ → ℝ), 0 < η → η ≤ 1 → 0 < K →
      ∀ (site : ℤ → ℕ → ℕ → ℤ) (a N : ℤ → ℕ),
      (∀ j ∈ bins, Real.exp (L ^ A / 2) ≤ (N j : ℝ)) →
      (∑ j ∈ bins, ∑ d ∈ D, ∑ q ∈ Q, uniformAverage (fun x : Fin (N j) =>
        paddingRejectionAtom data.Q d.primeFactors Q (actualPaddingBin η (c d) j) L K q
          ((a j + x.val : ℤ) + site j d q))) / paddingTiltNormalizer data.Q ≤
        (2 : ℝ) ^ J * (∏ j, primeHarmonicMass (P j)) * (C * (Real.log L)^(10 : ℕ) / K + L ^ (-90 : ℝ)) +
          (2 * bins.card * D.card * Q.card * Real.exp (-(L ^ 9))) /
            paddingTiltNormalizer data.Q := by
  obtain ⟨A, hA, hc⟩ := hBr.eventually_shifted_padding_comparison
  refine ⟨A, hA, ?_⟩
  intro a₀ ha₀
  obtain ⟨C, hC, hm⟩ := padding_holes_tuple_sum a₀ ha₀
  refine ⟨C, hC, ?_⟩
  filter_upwards [hc, hm, eventually_ge_atTop (1 : ℝ)] with L hc hm hL
  intro N₀ inst hN₀ hN₀log h J M B data hQ hB hpool hBL P hPeq hprime hdisjoint hJ D hD Q hQsub hqdegree
    bins η K c hη hηone hK site a N hN
  have hd (d : ℕ) (hd : d ∈ D) := primeTupleDivisors_arithmetic P hprime hdisjoint (hD hd)
  have he := hc h J M B data hB hpool hBL D
    (fun d hmem => ((hd d hmem).2.2.trans_eq hPeq).trans subset_union_left)
    (fun d hmem => by simpa only [(hd d hmem).2.1] using hJ)
    Q hQsub hqdegree bins η K c site a N hN
  have he' := (abs_le.mp he).2
  have hm' := hm N₀ hN₀ hN₀log h J M B data hQ hB D (fun _ => Q)
    (fun _ => bins) η K c (fun _ => 0)
    (fun d hdmem => ⟨(hd d hdmem).1,(hd d hdmem).2.1,(hd d hdmem).2.2.trans_eq hPeq⟩)
    (fun _ _ => hQsub) hη hηone hK
  simp only [add_zero] at hm'
  have hmass : (∑ d ∈ D, 1 / (d : ℝ)) ≤ ∏ j, primeHarmonicMass (P j) := by
    apply (sum_le_sum_of_subset_of_nonneg hD (fun d _ _ => by positivity)).trans_eq
    simpa only [primeHarmonicMass_eq_sum] using primeTupleDivisors_mass P hprime hdisjoint
  have hsmall : 0 ≤ C * (Real.log L)^(10 : ℕ) / K + L ^ (-90 : ℝ) := by positivity
  have hm'' : (data.residueLaw B hB).average (fun x => ∑ d ∈ D,
      positivePrimeWeight d.primeFactors (data.residueOrigin x) *
        paddingRejectedMass data.Q Q bins η (c d) L K (data.residueOrigin x)) ≤
      paddingTiltNormalizer data.Q * (∏ j, primeHarmonicMass (P j)) * (2 : ℝ)^J *
        (C * (Real.log L)^(10 : ℕ) / K + L ^ (-90 : ℝ)) := by
    rw [(data.residueLaw B hB).average_finset_sum]
    apply hm'.trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmass (paddingTiltNormalizer_pos data.Q).le) (by positivity)) hsmall
  have hS := paddingTiltNormalizer_pos data.Q
  have hx := (div_le_div_iff_of_pos_right hS).mpr he'
  rw [sub_div] at hx
  have hmNorm : (data.residueLaw B hB).average (fun x => ∑ d ∈ D,
      positivePrimeWeight d.primeFactors (data.residueOrigin x) *
        paddingRejectedMass data.Q Q bins η (c d) L K (data.residueOrigin x)) / paddingTiltNormalizer data.Q ≤
      (2 : ℝ)^J * (∏ j, primeHarmonicMass (P j)) *
        (C * (Real.log L)^(10 : ℕ) / K + L ^ (-90 : ℝ)) := by
    apply (div_le_iff₀ hS).mpr
    convert hm'' using 1 <;> ring
  linarith only [hx,hmNorm]

#print axioms reflected_shifted_padding_deletion
end ReflectedLiouville
