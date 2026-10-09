import ReflectedLiouville.ReflectedPartialReindex
import ReflectedLiouville.RoughConvolutionSaving
import ReflectedLiouville.BinGeometry
import ReflectedLiouville.ReflectedCompression

set_option autoImplicit false
open scoped BigOperators Classical
open OAI.TwoPointCorrelations

namespace ReflectedLiouville

/-- A nonempty narrow real bin gives an admissible integer dyadic block
    through its ceiling, without changing the real summation cutoff. -/
lemma ceiling_dyadic_slice (N : ℕ) (hN : 0 < N) (Y H B : ℝ) (Z : Finset ℕ)
    (hZ : Z.Nonempty) (hH : 2 ≤ H)
    (hrange : ∀ z ∈ Z, H ≤ (z : ℝ) ∧ Y / N ≤ (z : ℝ) ∧ (z : ℝ) < 2 * (Y / N) ∧ (z : ℝ) ≤ B) :
    let D := ⌈Y / N⌉₊
    H / 2 ≤ (D : ℝ) ∧ (D : ℝ) ≤ 2 * B ∧
      (N : ℝ) * D / 2 ≤ Y ∧ Y / N ≤ D ∧
      ∀ z ∈ Z, D ≤ z ∧ z < D + D := by
  dsimp only
  obtain ⟨z₀, hz₀⟩ := hZ
  obtain ⟨hHz, hRz, hzR, hzB⟩ := hrange z₀ hz₀
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hR1 : 1 ≤ Y / N := by linarith only [hHz, hzR, hH]
  have hR0 : 0 ≤ Y / N := by linarith
  have hceilLow := Nat.le_ceil (Y / N)
  have hceilHigh := (Nat.ceil_lt_add_one hR0).le
  have hD2 : (⌈Y / N⌉₊ : ℝ) ≤ 2 * (Y / N) := by linarith only [hceilHigh, hR1]
  refine ⟨by linarith only [hHz, hzR, hceilLow], by linarith only [hD2, hRz, hzB], ?_, hceilLow, ?_⟩
  · have hd := mul_le_mul_of_nonneg_left hD2 hNr.le
    have he : (N : ℝ) * (Y / N) = Y := by field_simp
    rw [show (N : ℝ) * (2 * (Y / N)) = 2 * ((N : ℝ) * (Y / N)) by ring, he] at hd
    linarith only [hd]
  · intro z hz
    obtain ⟨_, hlow, hhigh, _⟩ := hrange z hz
    constructor
    · exact Nat.ceil_le.mpr hlow
    · have hh : (z : ℝ) < (⌈Y / N⌉₊ : ℝ) + (⌈Y / N⌉₊ : ℝ) := by
        linarith only [hhigh, hceilLow]
      exact_mod_cast hh

lemma prime_slice_no_small_factor {J : ℕ} (P : Fin J → Finset ℕ) (I : Finset (Fin J))
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime) (R : ℝ)
    (hlarge : ∀ j, ∀ p ∈ P j, R ≤ (p : ℝ)) (z : ℕ) (hz : z ∈ primeTupleSlice P I) :
    HasNoPrimeFactorBelow R z := by
  intro p hp hsmall hdiv
  obtain ⟨j, hj, hpj⟩ := prime_dvd_primeTupleSlice P I hprime hz hp hdiv
  exact (not_lt_of_ge (hlarge j p hpj)) hsmall

lemma reflected_bin_slice_window (I : Finset (ℕ × ℕ)) (N q t z : ℕ)
    (hN : 0 < N) (hq : 0 < q) (ht : 0 < t) (hz : 0 < z)
    (η : ℝ) (hη : 0 < η) (hηsmall : η ≤ 1 / 2) (j : ℤ)
    (he : binPairEligible I η j (t * z) q) :
    let Y := reflectionBinCutoff N η j / ((q * t : ℕ) : ℝ)
    Y / N ≤ (z : ℝ) ∧ (z : ℝ) < 2 * (Y / N) := by
  dsimp only
  have ha : 0 < (t * z) * q := by positivity
  have hcut := actual_pair_bin_cutoff_bounds N ((t * z) * q) ha η hη
  have hbin : paddingBin η 0 (Real.log (((t * z) * q : ℕ) : ℝ)) = j := he.2
  rw [hbin] at hcut
  change (1 - η) * (((t * z) * q : ℕ) : ℝ) * N ≤ reflectionBinCutoff N η j ∧
    reflectionBinCutoff N η j ≤ (((t * z) * q : ℕ) : ℝ) * N at hcut
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hQr : (0 : ℝ) < q := by exact_mod_cast hq
  have hTr : (0 : ℝ) < t := by exact_mod_cast ht
  have hZr : (0 : ℝ) < z := by exact_mod_cast hz
  have hden : (0 : ℝ) < ((q * t : ℕ) : ℝ) := by positivity
  push_cast at hcut hden ⊢
  constructor
  · apply (div_le_iff₀ hNr).mpr
    apply (div_le_iff₀ (mul_pos hQr hTr)).mpr
    nlinarith only [hcut.2]
  · have hstrict : (1 / 2 : ℝ) * (t * z * q) * N < reflectionBinCutoff N η j := by
      have hbinBounds := (paddingBin_eq_iff η 0 (Real.log (((t * z) * q : ℕ) : ℝ)) j hη).mp hbin
      have hExp : Real.exp (-η) > (1 / 2 : ℝ) := by
        have hh := Real.add_one_lt_exp (show -η ≠ 0 by linarith)
        linarith only [hh, hηsmall]
      have he := Real.exp_le_exp.mpr (show Real.log (((t * z) * q : ℕ) : ℝ) - η ≤ (j : ℝ) * η by
        linarith [hbinBounds.2])
      rw [Real.exp_sub, Real.exp_log (by positivity)] at he
      have hid : (((t * z) * q : ℕ) : ℝ) / Real.exp η =
          (((t * z) * q : ℕ) : ℝ) * Real.exp (-η) := by rw [Real.exp_neg]; ring
      rw [hid] at he
      have hp := mul_lt_mul_of_pos_left hExp (by positivity : (0 : ℝ) < (((t * z) * q : ℕ) : ℝ))
      have hf := mul_lt_mul_of_pos_right (hp.trans_le he) hNr
      unfold reflectionBinCutoff
      push_cast at hf
      nlinarith only [hf]
    rw [show 2 * (reflectionBinCutoff N η j / ((q : ℝ) * t) / N) =
      (2 * reflectionBinCutoff N η j / ((q : ℝ) * t)) / N by ring]
    apply (lt_div_iff₀ hNr).mpr
    apply (lt_div_iff₀ (mul_pos hQr hTr)).mpr
    nlinarith only [hstrict]

#print axioms ceiling_dyadic_slice
#print axioms reflected_bin_slice_window
end ReflectedLiouville
