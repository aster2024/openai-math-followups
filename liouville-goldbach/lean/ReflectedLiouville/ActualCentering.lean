import ReflectedLiouville.ReflectionFiniteGeometry

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Filter
open scoped BigOperators Classical
open OAI.TwoPointCorrelations Finset

namespace ReflectedLiouville

theorem actual_centering_bin_saving (h_KMT : KMTInput) (h_MRT : MRTRealTwistRepulsionInput)
    (A : ℕ) (hA : 1000 ≤ A) (W δ : ℝ) (hW : 1 ≤ W)
    (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 100000) :
    ∃ C L₀ : ℝ, 0 < C ∧ 1 ≤ L₀ ∧ ∃ N₀ : ℕ, 3 ≤ N₀ ∧
      ∀ L : ℝ, L₀ ≤ L → ∀ (N : ℕ) [NeZero N], N₀ ≤ N → Real.log (N : ℝ) = L ^ A →
        ∀ (hL : 1 ≤ L) (η : ℝ), 0 < η → η ≤ 1 / 2 →
          let J := reflectionBandCount W δ L
          let data := reflectionPrimeFamily N W δ L η hL (by linarith)
          let P := centeredPrimeBands N.primeFactors (L ^ (1-δ)) W J
          ∀ j : ℤ, |centeredBinForm data.pairs N η j - rawBinForm data.pairs N η j| ≤
            C * L ^ (-1 - convolutionFinalExponent) * (2 : ℝ) ^ J * paddingTiltNormalizer data.Q *
              ∏ k, primeHarmonicMass (P k) := by
  obtain ⟨C,L₁,hC,hL₁,N₀,hN₀,hb⟩ := reflected_centering_bin_saving h_KMT h_MRT A hA
  obtain ⟨L₂,hL₂⟩ := eventually_atTop.mp
    (eventually_reflection_pool_range (A : ℝ) W δ hW hδ (by linarith))
  refine ⟨C,max L₁ L₂,hC,hL₁.trans (le_max_left _ _),N₀,hN₀,?_⟩
  intro L hL N inst hN hlog hLone η hη hηsmall
  dsimp only
  let J := reflectionBandCount W δ L
  let data := reflectionPrimeFamily N W δ L η hLone (by linarith : 0 ≤ W)
  let P := centeredPrimeBands N.primeFactors (L ^ (1-δ)) W J
  let Q := boundedPaddingDivisors data.Q ⌊100 * Real.log L⌋₊
  have hNlog : Real.log (N : ℝ) ≤ L ^ (A : ℝ) := by
    simpa only [Real.rpow_natCast] using hlog.le
  have hrange := hL₂ L ((le_max_right _ _).trans hL) N hNlog hLone η
  have hmass (k : Fin J) : 1 ≤ primeHarmonicMass (P k) := hW.trans (hrange.bandsLower k)
  have hlarge (k : Fin J) (p : ℕ) (hp : p ∈ P k) :
      Real.exp (L ^ convolutionSizeExponent) ≤ (p : ℝ) := by
    have hpow := Real.rpow_le_rpow_of_exponent_le hLone
      (show convolutionSizeExponent ≤ 1-δ by norm_num [convolutionSizeExponent]; linarith)
    have hceil := hrange.centerPrimeLower p (hrange.bandSubset k hp)
    have hpR : (⌈Real.exp (L ^ (1-δ))⌉₊ : ℝ) ≤ p := by exact_mod_cast hceil
    exact (Real.exp_le_exp.mpr hpow).trans ((Nat.le_ceil _).trans hpR)
  have hfull := reflection_full_tuple_upper N W δ L hLone hW hδ.le
  have hsub := reflection_pair_supply_subset N W δ L η hLone (by linarith : 0 ≤ W)
  have hQpos := fun q hq => bounded_padding_positive data q hq
  have hcop := fun q hq k p hp => bounded_padding_center_coprime data P hrange.bandSubset q hq k p hp
  have hV : 0 ≤ ∏ k, primeHarmonicMass (P k) := prod_nonneg (fun k _ => zero_le_one.trans (hmass k))
  have hLpos : 0 < L := by linarith
  intro j
  rw [centering_bin_profile_difference P hrange.bandPrimes hrange.bandDisjoint Q data.pairs hsub N η j]
  have he := hb L ((le_max_left _ _).trans hL) N hN hlog J P hrange.bandPrimes hrange.bandDisjoint
    hmass hlarge hfull Q actualPaddingCoefficient hQpos (fun q _ => actualPaddingCoefficient_nonneg q)
    hcop data.pairs η hη hηsmall j
  dsimp only at he
  apply he.trans
  apply mul_le_mul_of_nonneg_right _ hV
  apply mul_le_mul_of_nonneg_left (bounded_padding_mass data)
  positivity

lemma sum_bin_log_saving (bins : Finset ℤ) (F : ℤ → ℝ) (L η C E s : ℝ)
    (hL : 1 ≤ L) (hη : 0 < η) (hC : 0 ≤ C) (hE : 0 ≤ E)
    (hcard : (bins.card : ℝ) ≤ 101 * L / η)
    (hb : ∀ j ∈ bins, |F j| ≤ C * L ^ (-1-s) * E) :
    (∑ j ∈ bins, |F j|) ≤ 101 * C / η * E * L ^ (-s) := by
  have hLpos : 0 < L := by linarith
  have hscale : L * L ^ (-1-s) = L ^ (-s) := by
    nth_rewrite 1 [← Real.rpow_one L]
    rw [← Real.rpow_add hLpos]
    congr 1
    ring
  calc
    _ ≤ ∑ _j ∈ bins, C * L ^ (-1-s) * E := sum_le_sum hb
    _ = (bins.card : ℝ) * (C * L ^ (-1-s) * E) := by simp only [sum_const, nsmul_eq_mul]
    _ ≤ (101 * L / η) * (C * L ^ (-1-s) * E) := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 101 * C / η * E * (L * L ^ (-1-s)) := by ring
    _ = _ := by rw [hscale]

#print axioms actual_centering_bin_saving
#print axioms sum_bin_log_saving
end ReflectedLiouville
