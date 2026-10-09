import ReflectedLiouville.RawBinProfiles
import OAI.NumberTheory.TwoPoint.Bounds.VariableDegreeDeletion

set_option autoImplicit false
open scoped BigOperators Classical
open OAI.TwoPointCorrelations Finset

namespace ReflectedLiouville

lemma bounded_padding_positive {h J M : ℕ} (data : ProhibitedPrimeFamily h J M)
    (q : ℕ) (hq : q ∈ boundedPaddingDivisors data.Q M) : 0 < q := by
  have hs := retainedPrimeDivisor_squarefree data.Q data.primeQ (mem_filter.mp hq).1
  exact Nat.pos_of_ne_zero hs.ne_zero

lemma bounded_padding_mass {h J M : ℕ} (data : ProhibitedPrimeFamily h J M) :
    (∑ q ∈ boundedPaddingDivisors data.Q M, actualPaddingCoefficient q / (q : ℝ)) ≤
      paddingTiltNormalizer data.Q :=
  retained_padding_mass_le data.Q _ data.primeQ (filter_subset _ _)

lemma bounded_padding_center_coprime {h J M : ℕ} (data : ProhibitedPrimeFamily h J M)
    (P : Fin J → Finset ℕ) (hsub : ∀ j, P j ⊆ data.P)
    (q : ℕ) (hq : q ∈ boundedPaddingDivisors data.Q M) (j : Fin J) (p : ℕ) (hp : p ∈ P j) :
    q.Coprime p := by
  have hret := (mem_filter.mp hq).1
  have hq0 := (retainedPrimeDivisor_squarefree data.Q data.primeQ hret).ne_zero
  have hprime := data.primeP p (hsub j hp)
  apply Nat.coprime_comm.mpr
  apply hprime.coprime_iff_not_dvd.mpr
  intro hdiv
  have hpf : p ∈ q.primeFactors := Nat.mem_primeFactors.mpr ⟨hprime, hdiv, hq0⟩
  have hpQ := retainedPrimeDivisor_factors data.Q data.primeQ hret hpf
  exact disjoint_left.mp data.disjoint (hsub j hp) hpQ

lemma reflection_pair_supply_subset (N : ℕ) [NeZero N] (W δ L η : ℝ)
    (hL : 1 ≤ L) (hW : 0 ≤ W) :
    let data := reflectionPrimeFamily N W δ L η hL hW
    let P := centeredPrimeBands N.primeFactors (L ^ (1-δ)) W (reflectionBandCount W δ L)
    data.pairs ⊆ primeTupleDivisors P ×ˢ boundedPaddingDivisors data.Q ⌊100 * Real.log L⌋₊ := by
  dsimp only [reflectionPrimeFamily, actualProhibitedPrimeFamily]
  unfold primeFamilyPairs
  rw [Finset.product_eq_sprod]
  exact filter_subset _ _

lemma reflection_band_union (N : ℕ) [NeZero N] (W δ L η : ℝ)
    (hL : 1 ≤ L) (hW : 0 ≤ W) :
    let data := reflectionPrimeFamily N W δ L η hL hW
    let P := centeredPrimeBands N.primeFactors (L ^ (1-δ)) W (reflectionBandCount W δ L)
    univ.biUnion P = data.P := rfl

lemma reflection_full_tuple_upper (N : ℕ) [NeZero N] (W δ L : ℝ)
    (hL : 1 ≤ L) (hW : 1 ≤ W) (hδ : 0 ≤ δ) :
    ∀ d ∈ primeTupleDivisors
      (centeredPrimeBands N.primeFactors (L ^ (1-δ)) W (reflectionBandCount W δ L)),
      (d : ℝ) ≤ Real.exp (2 * L) := by
  intro d hd
  have hAp : 0 < L ^ (1-δ) := Real.rpow_pos_of_pos (by linarith) _
  have hb := centeredPrimeTuple_log_bound hAp hW
    (reflection_prime_endpoint W δ L (by linarith) hδ hL) hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast hb.1
  simpa only [Real.exp_log hdR] using Real.exp_le_exp.mpr hb.2

#print axioms bounded_padding_center_coprime
#print axioms reflection_pair_supply_subset
end ReflectedLiouville
