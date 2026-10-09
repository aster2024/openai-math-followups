import ReflectedLiouville.ReflectionPrimeFamily
import OAI.NumberTheory.TwoPoint.Bounds.PrimeTraceParameters

set_option autoImplicit false
open Filter
open scoped BigOperators Classical
open OAI.TwoPointCorrelations

namespace ReflectedLiouville

lemma reflection_degree_budget (W δ L : ℝ) (hW : 1 ≤ W) (hδ : 0 ≤ δ) (hδ₁ : δ ≤ 1) (hL : 1 ≤ L) :
    ((reflectionBandCount W δ L + ⌊100 * Real.log L⌋₊ : ℕ) : ℝ) ≤ 101 * Real.log L ∧
      (⌊100 * Real.log L⌋₊ : ℝ) ≤ 100 * Real.log L ∧
      (reflectionBandCount W δ L : ℝ) * (6 * W) ≤ Real.log L := by
  have hlog : 0 ≤ Real.log L := Real.log_nonneg hL
  have hc := reflectionBandCount_mul_bound W δ L (by linarith) hδ hL
  have hc' : (reflectionBandCount W δ L : ℝ) * (6 * W) ≤ Real.log L := hc.trans (by nlinarith)
  have hprod : (reflectionBandCount W δ L : ℝ) ≤ reflectionBandCount W δ L * (6 * W) := by
    have hb := mul_le_mul_of_nonneg_left hW (show (0 : ℝ) ≤ reflectionBandCount W δ L by positivity)
    nlinarith
  have hj := hprod.trans hc'
  have hm : (⌊100 * Real.log L⌋₊ : ℝ) ≤ 100 * Real.log L := Nat.floor_le (by positivity)
  refine ⟨?_, hm, hc'⟩
  push_cast
  linarith

/-- This internal numerical range is proved for the actual prime family. -/
structure ReflectionPoolRange {h J M : ℕ} (data : ProhibitedPrimeFamily h J M)
    (P : Fin J → Finset ℕ) (L W α : ℝ) : Prop where
  oneJ : 1 ≤ J
  slots : ((J + M : ℕ) : ℝ) ≤ 101 * Real.log L
  paddingDegree : (M : ℝ) ≤ 100 * Real.log L
  bandsLower : ∀ j, W ≤ primeHarmonicMass (P j)
  bandsUpper : ∀ j, primeHarmonicMass (P j) ≤ 2 * W
  bandsPolynomial : ∀ j, primeHarmonicMass (P j) ≤ L ^ (2 : ℕ)
  bandSubset : ∀ j, P j ⊆ data.P
  bandDisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l)
  bandPrimes : ∀ j, ∀ p ∈ P j, p.Prime
  centerLower : 1 ≤ primeHarmonicMass data.P
  centerUpper : primeHarmonicMass data.P ≤ L ^ (2 : ℕ)
  centerW : (∑ p ∈ data.P, 1 / (p : ℝ)) ≤ 2 * W * J
  paddingLog : (∑ p ∈ data.Q, 1 / (p : ℝ)) ≤ Real.log L
  paddingUpper : primeHarmonicMass data.Q ≤ L ^ (2 : ℕ)
  countW : (J : ℝ) * (6 * W) ≤ Real.log L
  residueBound : ∀ p ∈ data.P ∪ data.Q, p ≤ ⌊Real.exp L⌋₊
  centerPrimeLower : ∀ p ∈ data.P, ⌈Real.exp (L ^ α)⌉₊ ≤ p
  centerPrimeUpper : ∀ p ∈ data.P, p ≤ ⌊Real.exp L⌋₊

/-- All varying exclusions are after the single threshold in L. -/
theorem eventually_reflection_pool_range (a W δ : ℝ) (hW : 1 ≤ W)
    (hδ : 0 < δ) (hδ₁ : δ < 1) :
    ∀ᶠ L : ℝ in atTop, ∀ (N : ℕ) [NeZero N], Real.log (N : ℝ) ≤ L ^ a →
      ∀ (hL : 1 ≤ L) (η : ℝ),
        let data := reflectionPrimeFamily N W δ L η hL (by linarith)
        let P := centeredPrimeBands N.primeFactors (L ^ (1 - δ)) W (reflectionBandCount W δ L)
        ReflectionPoolRange data P L W (1 - δ) := by
  filter_upwards [eventually_center_band_masses a (1 - δ) W (by linarith) (by linarith),
    eventually_reflectionBandCount_positive W δ (by linarith) hδ,
    modFiveThetaInput.eventually_padding_pool_mass ∅, eventually_ge_atTop (1 : ℝ)]
      with L hmass hJ hQfull hL₀
  intro N inst hN hL η
  dsimp only
  let J := reflectionBandCount W δ L
  let data := reflectionPrimeFamily N W δ L η hL (by linarith : 0 ≤ W)
  let P := centeredPrimeBands N.primeFactors (L ^ (1 - δ)) W J
  have hAp : 0 < L ^ (1 - δ) := Real.rpow_pos_of_pos (by linarith) _
  have hWp : 0 < W := by linarith
  have hv (j : Fin J) : W ≤ primeHarmonicMass (P j) ∧ primeHarmonicMass (P j) ≤ 2 * W := hmass N hN j.val
  have hpool := centeredPrimePool_mass_bounds N.primeFactors (L ^ (1 - δ)) W J hAp.le hWp.le hv
  have hbudget := reflection_degree_budget W δ L hW hδ.le hδ₁.le hL
  have hJr : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  have hlog : 0 ≤ Real.log L := Real.log_nonneg hL
  have hlogL : Real.log L ≤ L := (Real.log_le_sub_one_of_pos (by linarith : 0 < L)).trans (by linarith)
  have hLsq : L ≤ L ^ (2 : ℕ) := by nlinarith
  have hPlo : 1 ≤ primeHarmonicMass data.P := by
    have hJW : (1 : ℝ) ≤ (J : ℝ) * W := by nlinarith
    exact hJW.trans hpool.1
  have hPupper : primeHarmonicMass data.P ≤ L ^ (2 : ℕ) := by
    have hPW : primeHarmonicMass data.P ≤ (J : ℝ) * (2 * W) := hpool.2
    have hcount : (J : ℝ) * (6 * W) ≤ Real.log L := hbudget.2.2
    have hsmall : primeHarmonicMass data.P ≤ Real.log L := by nlinarith
    exact hsmall.trans (hlogL.trans hLsq)
  have hQlog : (∑ p ∈ data.Q, 1 / (p : ℝ)) ≤ Real.log L := by
    rw [← primeHarmonicMass_eq_sum]
    exact (primeHarmonicMass_mono (paddingPrimeSupply_subset_empty N.primeFactors L)).trans hQfull
  have hsub := centeredPrimeBand_subset_pool N.primeFactors (L ^ (1 - δ)) W J
  have hE : ∀ p : ℕ, p.Prime → p ∣ N → p ∈ N.primeFactors :=
    fun p hp hdiv => Nat.mem_primeFactors.mpr ⟨hp, hdiv, NeZero.ne N⟩
  have hend := reflection_prime_endpoint W δ L hWp hδ.le hL
  refine ⟨hJ, hbudget.1, hbudget.2.1, (fun j => (hv j).1), (fun j => (hv j).2),
    (fun j => (primeHarmonicMass_mono (hsub j)).trans hPupper), hsub,
    centeredPrimeBands_disjoint N.primeFactors (L ^ (1 - δ)) W J hAp.le hWp.le,
    centeredPrimeBands_prime N.primeFactors (L ^ (1 - δ)) W J,
    hPlo, hPupper, ?_, hQlog, ?_, hbudget.2.2, ?_, ?_, ?_⟩
  · rw [← primeHarmonicMass_eq_sum]
    have hpW : primeHarmonicMass data.P ≤ (J : ℝ) * (2 * W) := hpool.2
    nlinarith only [hpW]
  · rw [primeHarmonicMass_eq_sum]
    exact hQlog.trans (hlogL.trans hLsq)
  · intro p hp
    exact actualProhibitedPrimeFamily_residue_bound N J ⌊100 * Real.log L⌋₊ N.primeFactors
      (L ^ (1 - δ)) W L (PaddingPairEligible L η) hAp.le hWp.le hE hend hp
  · intro p hp
    exact centeredPrimePool_lower_nat N.primeFactors (L ^ (1 - δ)) W L J hAp.le hWp.le hend hp
  · intro p hp
    exact actualProhibitedPrimeFamily_residue_bound N J ⌊100 * Real.log L⌋₊ N.primeFactors
      (L ^ (1 - δ)) W L (PaddingPairEligible L η) hAp.le hWp.le hE hend (Finset.mem_union_left _ hp)

#print axioms eventually_reflection_pool_range

end ReflectedLiouville
