import ReflectedLiouville.QuotientConvolutionIdentity
import ReflectedLiouville.QuotientFourier

set_option autoImplicit false
open scoped BigOperators Classical
open OAI.TwoPointCorrelations

namespace ReflectedLiouville

lemma circle_character_eq_additive (k : ℕ) (θ : ℝ) :
    fourier (k : ℤ) (θ : AddCircle (1 : ℝ)) = additiveCharacter θ k := by
  rw [fourier_coe_apply]
  unfold additiveCharacter
  congr 1
  push_cast
  ring

lemma quotient_prefix_all_below (N r : ℕ) (Y : ℝ) (hN : 0 < N) (hr : r ≤ N) (hY : 0 ≤ Y)
    (k : ℕ) (hk : k < ⌊Y / N⌋₊) : ((N * k + r : ℕ) : ℝ) ≤ Y := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hf : (⌊Y / N⌋₊ : ℝ) ≤ Y / N := Nat.floor_le (div_nonneg hY hNr.le)
  have hNK : ((N * ⌊Y / N⌋₊ : ℕ) : ℝ) ≤ Y := by
    have hp := (le_div_iff₀ hNr).mp hf
    simpa only [Nat.cast_mul, mul_comm] using hp
  have hnat : N * k + r ≤ N * ⌊Y / N⌋₊ := by
    calc
      _ ≤ N * k + N := Nat.add_le_add_left hr _
      _ = N * (k + 1) := by ring
      _ ≤ _ := Nat.mul_le_mul_left N (by omega)
  exact (show ((N * k + r : ℕ) : ℝ) ≤ ((N * ⌊Y / N⌋₊ : ℕ) : ℝ) by exact_mod_cast hnat).trans hNK

/-- Prefix lengths across residues differ by at most the single endpoint term. -/
theorem quotient_circle_prefix_identity (N r : ℕ) (Y θ : ℝ)
    (hN : 0 < N) (hr : r ≤ N) (hY : 0 ≤ Y) :
    quotientSourcePolynomial N r Y (θ : AddCircle (1 : ℝ)) =
      quotientExponentialSum N (Y / N) r θ +
        if (((N * ⌊Y / N⌋₊ + r : ℕ) : ℝ) ≤ Y) then
          liouville (N * ⌊Y / N⌋₊ + r) * additiveCharacter θ ⌊Y / N⌋₊ else 0 := by
  unfold quotientSourcePolynomial fourierPolynomial quotientPrefixIndices
  rw [Finset.sum_filter, Finset.sum_range_succ]
  simp only [circle_character_eq_additive]
  congr 1
  unfold quotientExponentialSum
  apply Finset.sum_congr rfl
  intro k hk
  rw [ite_eq_left (quotient_prefix_all_below N r Y hN hr hY k (Finset.mem_range.mp hk))]

lemma quotient_circle_prefix_norm (N r : ℕ) (Y θ : ℝ)
    (hN : 0 < N) (hr : r ≤ N) (hY : 0 ≤ Y) :
    ‖quotientSourcePolynomial N r Y (θ : AddCircle (1 : ℝ))‖ ≤
      ‖quotientExponentialSum N (Y / N) r θ‖ + 1 := by
  rw [quotient_circle_prefix_identity N r Y θ hN hr hY]
  apply (norm_add_le _ _).trans
  apply add_le_add le_rfl
  split_ifs
  · rw [norm_mul, norm_additiveCharacter, mul_one]
    exact norm_liouville_le _
  · norm_num

/-- The exact circle-prefix Fourier estimate used by centering, retaining the
    one endpoint term rather than replacing different prefixes silently. -/
theorem quotient_circle_prefix_mean (h_KMT : KMTInput) (h_MRT : MRTRealTwistRepulsionInput) :
    ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, 3 ≤ N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ Y : ℝ,
        Real.exp ((Real.log (N : ℝ)) ^ ν) ≤ Y / N → Y / N ≤ N →
          ∀ ξ : AddCircle (1 : ℝ),
            (∑ r ∈ Finset.Icc 1 N, ‖quotientSourcePolynomial N r Y ξ‖) / (N : ℝ) ≤
              C * (Y / N) / Real.rpow (Real.log (Y / N)) (1 / 3000) + 1 := by
  intro ν hν hν₁
  obtain ⟨C, hC, N₀, hN₀, hfourier⟩ := quotient_liouville_fourier h_KMT h_MRT ν hν hν₁
  refine ⟨C, hC, N₀, hN₀, ?_⟩
  intro N hN Y hYlow hYhigh ξ
  have hn : 0 < N := by have := hN₀.trans hN; omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hn
  have hratio : 0 < Y / N := (Real.exp_pos _).trans_le hYlow
  have hY : 0 ≤ Y := by
    have hp := mul_nonneg hratio.le hNr.le
    rwa [div_mul_cancel₀ Y hNr.ne'] at hp
  obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective ξ
  have hs : (∑ r ∈ Finset.Icc 1 N, ‖quotientSourcePolynomial N r Y (θ : AddCircle (1 : ℝ))‖) ≤
      (∑ r ∈ Finset.Icc 1 N, ‖quotientExponentialSum N (Y / N) r θ‖) + (N : ℝ) := by
    calc
      _ ≤ ∑ r ∈ Finset.Icc 1 N, (‖quotientExponentialSum N (Y / N) r θ‖ + 1) := by
        apply Finset.sum_le_sum
        intro r hr
        exact quotient_circle_prefix_norm N r Y θ hn (Finset.mem_Icc.mp hr).2 hY
      _ = _ := by simp [Finset.sum_add_distrib]
  have hdiv := div_le_div_of_nonneg_right hs hNr.le
  have hq := hfourier N hN (Y / N) hYlow hYhigh θ
  have hid : ((∑ r ∈ Finset.Icc 1 N, ‖quotientExponentialSum N (Y / N) r θ‖) + (N : ℝ)) / N =
      (∑ r ∈ Finset.Icc 1 N, ‖quotientExponentialSum N (Y / N) r θ‖) / N + 1 := by
    rw [add_div, div_self hNr.ne']
  rw [hid] at hdiv
  linarith only [hdiv, hq]

#print axioms quotient_circle_prefix_mean

end ReflectedLiouville
