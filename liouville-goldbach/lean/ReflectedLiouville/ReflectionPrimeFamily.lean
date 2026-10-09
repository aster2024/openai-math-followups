import ReflectedLiouville.ReflectionPrimeGeometry
import ReflectedLiouville.CRTTransport

set_option autoImplicit false
open scoped BigOperators Classical
open OAI.TwoPointCorrelations

namespace ReflectedLiouville

noncomputable def reflectionPrimeFamily (N : ℕ) [NeZero N] (W δ L η : ℝ)
    (hL : 1 ≤ L) (hW : 0 ≤ W) :
    ProhibitedPrimeFamily N (reflectionBandCount W δ L) ⌊100 * Real.log L⌋₊ :=
  actualProhibitedPrimeFamily N (reflectionBandCount W δ L) ⌊100 * Real.log L⌋₊
    N.primeFactors (L ^ (1 - δ)) W L (PaddingPairEligible L η)
    (Real.rpow_nonneg (by linarith) _) hW
    (fun p hp hdiv => Nat.mem_primeFactors.mpr ⟨hp, hdiv, NeZero.ne N⟩)

lemma reflection_pool_coprime_total (N : ℕ) [NeZero N] (W δ L η : ℝ)
    (hL : 1 ≤ L) (hW : 0 ≤ W) (p : ℕ)
    (hp : p ∈ (reflectionPrimeFamily N W δ L η hL hW).P ∪
      (reflectionPrimeFamily N W δ L η hL hW).Q) : Nat.Coprime p N := by
  let data := reflectionPrimeFamily N W δ L η hL hW
  have hprime : p.Prime := data.prime ⟨p, hp⟩
  apply hprime.coprime_iff_not_dvd.mpr
  intro hdiv
  have hpf : p ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hprime, hdiv, NeZero.ne N⟩
  rcases Finset.mem_union.mp hp with hpP | hpQ
  · obtain ⟨j, hj⟩ := mem_primeTuplePool.mp hpP
    exact (centeredPrimeSupply_mem hj).2.2.1 hpf
  · exact (Finset.mem_sdiff.mp hpQ).2 hpf

lemma reflection_pair_coprime_total (N : ℕ) [NeZero N] (W δ L η : ℝ)
    (hL : 1 ≤ L) (hW : 0 ≤ W) (d q : ℕ)
    (hdq : (d, q) ∈ (reflectionPrimeFamily N W δ L η hL hW).pairs) :
    Nat.Coprime (q * d) N := by
  let data := reflectionPrimeFamily N W δ L η hL hW
  have hs := data.whole_squarefree (d, q) hdq
  apply (Nat.disjoint_primeFactors hs.ne_zero (NeZero.ne N)).mp
  apply Finset.disjoint_left.mpr
  intro p hp hpf
  have hpool : p ∈ data.P ∪ data.Q := by
    rw [Nat.primeFactors_mul (data.padding_squarefree _ hdq).ne_zero
      (data.tuple_squarefree _ hdq).ne_zero] at hp
    rcases Finset.mem_union.mp hp with hpq | hpd
    · exact Finset.mem_union_right _ (data.padding_pool _ hdq hpq)
    · exact Finset.mem_union_left _ (data.tuple_pool _ hdq hpd)
  have hcop := reflection_pool_coprime_total N W δ L η hL hW p hpool
  exact ((Nat.mem_primeFactors.mp hpf).1.coprime_iff_not_dvd.mp hcop)
    (Nat.mem_primeFactors.mp hpf).2.1

/-- The numerical support/cap statements used in both the physical and CRT
    quotient graphs, proved from the literal retained pair construction. -/
theorem reflection_family_support (N : ℕ) [NeZero N] (W δ L η : ℝ)
    (hL : 1 ≤ L) (hW : 1 ≤ W) (hδ : 0 ≤ δ) (hη : 0 < η) (hη₁ : η ≤ 1) :
    let data := reflectionPrimeFamily N W δ L η hL (by linarith)
    (∀ dq ∈ data.pairs,
      dq.2 ≤ ⌊Real.exp (100 * L + 1)⌋₊ ∧
      Real.log (dq.1 : ℝ) ≤ 2 * L ∧ Nat.Coprime (dq.2 * dq.1) N) ∧
      (data.pairs.card : ℝ) ≤ Real.exp (101 * L) := by
  dsimp only
  let data := reflectionPrimeFamily N W δ L η hL (by linarith : 0 ≤ W)
  have hAp : 0 < L ^ (1 - δ) := Real.rpow_pos_of_pos (by linarith) _
  have hE : ∀ p : ℕ, p.Prime → p ∣ N → p ∈ N.primeFactors :=
    fun p hp hdiv => Nat.mem_primeFactors.mpr ⟨hp, hdiv, NeZero.ne N⟩
  have he : ∀ d q, PaddingPairEligible L η d q → PaddingPairEligible L η d q := fun _ _ h => h
  constructor
  · intro dq hdq
    have hm := (actualProhibitedPrimeFamily_pairs N (reflectionBandCount W δ L) ⌊100 * Real.log L⌋₊
      N.primeFactors (L ^ (1 - δ)) W L (PaddingPairEligible L η) hAp.le (by linarith) hE dq.1 dq.2).mp hdq
    refine ⟨paddingPairEligible_padding_upper hη hη₁
      (Nat.pos_of_ne_zero (data.tuple_squarefree _ hdq).ne_zero) hm.2.2.2, ?_,
      reflection_pair_coprime_total N W δ L η hL (by linarith) _ _ hdq⟩
    exact (centeredPrimeTuple_log_bound hAp hW
      (reflection_prime_endpoint W δ L (by linarith) hδ hL) hm.1).2
  · exact actualProhibitedPrimeFamily_pairs_card N (reflectionBandCount W δ L) ⌊100 * Real.log L⌋₊
      N.primeFactors (L ^ (1 - δ)) W L η (PaddingPairEligible L η) hAp.le (by linarith) hE hL hη hη₁ he

#print axioms reflection_family_support

end ReflectedLiouville
