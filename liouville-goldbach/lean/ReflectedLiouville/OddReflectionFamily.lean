import ReflectedLiouville.CRTInverse
import ReflectedLiouville.PrimeFamilyRebase

set_option autoImplicit false
open Filter
open scoped BigOperators Classical
open OAI.TwoPointCorrelations

namespace ReflectedLiouville

lemma total_double_nonzero (N : ℕ) [NeZero N] : 2 * N ≠ 0 := Nat.mul_ne_zero (by decide) (NeZero.ne N)

/-- The single fixed prime 2 is excluded by using (2N).primeFactors as the
    pool exclusion set. The reflected total remains N. -/
noncomputable def oddReflectionPrimeFamily (N : ℕ) [NeZero N] (W δ L η : ℝ)
    (hL : 1 ≤ L) (hW : 0 ≤ W) :
    ProhibitedPrimeFamily N (reflectionBandCount W δ L) ⌊100 * Real.log L⌋₊ := by
  letI : NeZero (2 * N) := ⟨total_double_nonzero N⟩
  let data := reflectionPrimeFamily (2 * N) W δ L η hL hW
  exact rebasePrimeFamily data N (fun p hp hdiv => data.excluded p hp (hdiv.trans (dvd_mul_left N 2)))

lemma odd_reflection_pool_primes (N : ℕ) [NeZero N] (W δ L η : ℝ)
    (hL : 1 ≤ L) (hW : 0 ≤ W) (p : ℕ)
    (hp : p ∈ (oddReflectionPrimeFamily N W δ L η hL hW).P ∪
      (oddReflectionPrimeFamily N W δ L η hL hW).Q) : Odd p := by
  letI : NeZero (2 * N) := ⟨total_double_nonzero N⟩
  let data := reflectionPrimeFamily (2 * N) W δ L η hL hW
  have hprime : p.Prime := data.prime ⟨p, hp⟩
  have hp2 : p ≠ 2 := by
    intro heq
    subst p
    have hpf : 2 ∈ (2 * N).primeFactors := Nat.mem_primeFactors.mpr
      ⟨by decide, dvd_mul_right 2 N, total_double_nonzero N⟩
    rcases Finset.mem_union.mp hp with hP | hQ
    · obtain ⟨j, hj⟩ := mem_primeTuplePool.mp hP
      exact (centeredPrimeSupply_mem hj).2.2.1 hpf
    · exact (Finset.mem_sdiff.mp hQ).2 hpf
  exact hprime.odd_of_ne_two hp2

lemma squarefree_odd_of_prime_pool (q : ℕ) (hq : Squarefree q) (P : Finset ℕ)
    (hpool : q.primeFactors ⊆ P) (hodd : ∀ p ∈ P, Odd p) : Odd q := by
  rw [← Nat.prod_primeFactors_of_squarefree hq]
  have hprod : ∀ S : Finset ℕ, (∀ p ∈ S, Odd p) → Odd (∏ p ∈ S, p) := by
    intro S
    induction S using Finset.induction_on with
    | empty => intro h; exact ⟨0, by simp⟩
    | @insert p S hnot ih =>
      intro h
      rw [Finset.prod_insert hnot]
      exact (h p (by simp)).mul (ih (fun q hq => h q (by simp [hq])))
  exact hprod q.primeFactors (fun p hp => hodd p (hpool hp))

theorem odd_reflection_pair_step (N : ℕ) [NeZero N] (W δ L η : ℝ)
    (hL : 1 ≤ L) (hW : 0 ≤ W) (dq : ℕ × ℕ)
    (hdq : dq ∈ (oddReflectionPrimeFamily N W δ L η hL hW).pairs) :
    Odd (dq.1 * dq.2) := by
  let data := oddReflectionPrimeFamily N W δ L η hL hW
  have hd : Odd dq.1 := squarefree_odd_of_prime_pool dq.1 (data.tuple_squarefree _ hdq) data.P
    (data.tuple_pool _ hdq) (fun p hp => odd_reflection_pool_primes N W δ L η hL hW p (Finset.mem_union_left _ hp))
  have hq : Odd dq.2 := squarefree_odd_of_prime_pool dq.2 (data.padding_squarefree _ hdq) data.Q
    (data.padding_pool _ hdq) (fun p hp => odd_reflection_pool_primes N W δ L η hL hW p (Finset.mem_union_right _ hp))
  exact hd.mul hq

#print axioms odd_reflection_pair_step

end ReflectedLiouville
