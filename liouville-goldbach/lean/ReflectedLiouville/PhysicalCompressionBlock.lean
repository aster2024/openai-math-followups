import ReflectedLiouville.CRTGraphTransport

set_option autoImplicit false
open scoped BigOperators Classical
open OAI.TwoPointCorrelations

namespace ReflectedLiouville

lemma quotient_compression_eq_block {N J M : ℕ}
    (data : ProhibitedPrimeFamily N J M) (P : Fin J → Finset ℕ)
    (ell b : ℕ) (r : ℤ) (L W : ℝ) (eligible : ℕ → ℕ → Prop) :
    quotientReflectionCompression data P
      (fun i : Fin ⌈Real.exp (103 * L)⌉₊ => (i.val : ℤ) - b) ell r L W eligible =
      reflectionCompressedGraph (quotientPrimeFamily data) P L W eligible (fun _ _ _ => True)
        ((ell : ℤ) * r - b) := by
  unfold quotientReflectionCompression reflectionCompressedGraph primeBlockCompression
  dsimp only [quotientPrimeFamily, rebasePrimeFamily]
  have hpoint (i : Fin ⌈Real.exp (103 * L)⌉₊) :
      (i.val : ℤ) - b + (ell : ℤ) * r = (i.val : ℤ) + ((ell : ℤ) * r - b) := by ring
  simp only [hpoint, true_and]

/-- Exact physical operator equality on the centered finite block. The cut
    predicates at negative physical sites are transported, not reinterpreted. -/
theorem physical_compression_eq_block {N J M B : ℕ}
    (data : ProhibitedPrimeFamily N J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (hN : 0 < N) (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l)) (hsub : ∀ j, P j ⊆ data.P)
    (hc : ∀ d q, (d, q) ∈ data.pairs → Nat.Coprime (q * d) N)
    (ell b : ℕ) (hinv : ∀ p : ↥(data.P ∪ data.Q), (N : ZMod p.val) * (ell : ZMod p.val) = 1)
    (r : ℤ) (L W : ℝ) (eligible : ℕ → ℕ → Prop) :
    physicalReflectionCompression data P
      (fun i : Fin ⌈Real.exp (103 * L)⌉₊ => (i.val : ℤ) - b) r L W eligible =
      reflectionCompressedGraph (quotientPrimeFamily data) P L W eligible (fun _ _ _ => True)
        ((ell : ℤ) * r - b) := by
  rw [reflected_compression_CRT data hB hN P hprime hdisjoint hsub hc _ ell hinv r L W eligible,
    quotient_compression_eq_block]

#print axioms physical_compression_eq_block

end ReflectedLiouville
