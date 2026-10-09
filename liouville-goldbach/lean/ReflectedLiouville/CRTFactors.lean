import ReflectedLiouville.ReflectedCompression
import ReflectedLiouville.CRTTransport

set_option autoImplicit false
open scoped BigOperators Classical
open OAI.TwoPointCorrelations

namespace ReflectedLiouville

lemma crt_prime_divisibility (N ell p : ℕ) (hinv : (N : ZMod p) * (ell : ZMod p) = 1)
    (k r : ℤ) :
    (p : ℤ) ∣ (N : ℤ) * k + r ↔ (p : ℤ) ∣ k + (ell : ℤ) * r := by
  have hcop : Nat.Coprime p N := (coprime_of_pool_inverse ell N p (by simpa only [mul_comm] using hinv)).symm
  have hm : (((N : ℤ) * k + r : ℤ) : ZMod p) =
      (((N : ℤ) * (k + (ell : ℤ) * r) : ℤ) : ZMod p) := by
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, mul_add, ← mul_assoc, hinv, one_mul]
  have hd : (p : ℤ) ∣ (N : ℤ) * k + r ↔ (p : ℤ) ∣ (N : ℤ) * (k + (ell : ℤ) * r) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd, hm]
  exact hd.trans (nat_scaled_dvd p N hcop _)

lemma crt_squarefree_divisibility (N ell d : ℕ) (P : Finset ℕ)
    (hd : Squarefree d) (hpool : d.primeFactors ⊆ P)
    (hinv : ∀ p ∈ P, (N : ZMod p) * (ell : ZMod p) = 1) (k r : ℤ) :
    (d : ℤ) ∣ (N : ℤ) * k + r ↔ (d : ℤ) ∣ k + (ell : ℤ) * r := by
  have hcop : Nat.Coprime d ell := by
    rw [← Nat.prod_primeFactors_of_squarefree hd]
    apply Nat.coprime_prod_left_iff.mpr
    intro p hp
    exact (coprime_of_pool_inverse N ell p (hinv p (hpool hp))).symm
  have hm : ∀ p ∈ P,
      (((ell : ℤ) * ((N : ℤ) * k + r) : ℤ) : ZMod p) = ((k + (ell : ℤ) * r : ℤ) : ZMod p) := by
    intro p hp
    simp only [Int.cast_mul, Int.cast_add, Int.cast_natCast, mul_add]
    rw [show (ell : ZMod p) * ((N : ZMod p) * (k : ZMod p)) =
      ((N : ZMod p) * (ell : ZMod p)) * (k : ZMod p) by ring, hinv p hp, one_mul]
  have hdv := squarefree_divisor_congr P d hd hpool ((ell : ℤ) * ((N : ℤ) * k + r))
    (k + (ell : ℤ) * r) hm
  exact (nat_scaled_dvd d ell hcop _).symm.trans hdv

lemma crt_padding_degree (N ell : ℕ) (Q : Finset ℕ)
    (hinv : ∀ p ∈ Q, (N : ZMod p) * (ell : ZMod p) = 1) (k r : ℤ) :
    actualPaddingDegree Q ((N : ℤ) * k + r) = actualPaddingDegree Q (k + (ell : ℤ) * r) := by
  unfold actualPaddingDegree
  congr 1
  ext p
  simp only [Finset.mem_filter]
  apply and_congr_right
  intro hp
  exact crt_prime_divisibility N ell p (hinv p hp) k r

lemma crt_padding_vertex (N ell : ℕ) (Q : Finset ℕ)
    (hinv : ∀ p ∈ Q, (N : ZMod p) * (ell : ZMod p) = 1) (k r : ℤ) :
    actualPaddingVertex Q ((N : ℤ) * k + r) = actualPaddingVertex Q (k + (ell : ℤ) * r) := by
  unfold actualPaddingVertex actualPaddingWeight
  rw [crt_padding_degree N ell Q hinv k r]

lemma crt_centered_tuple (N ell : ℕ) (P S : Finset ℕ) (hS : S ⊆ P)
    (hinv : ∀ p ∈ P, (N : ZMod p) * (ell : ZMod p) = 1) (k r : ℤ) :
    centeredTuple S ((N : ℤ) * k + r) = centeredTuple S (k + (ell : ℤ) * r) := by
  unfold centeredTuple
  apply Finset.prod_congr rfl
  intro p hp
  simp only [crt_prime_divisibility N ell p (hinv p (hS hp)) k r]

lemma crt_positive_prime_weight (N ell : ℕ) (P S : Finset ℕ) (hS : S ⊆ P)
    (hinv : ∀ p ∈ P, (N : ZMod p) * (ell : ZMod p) = 1) (k r : ℤ) :
    positivePrimeWeight S ((N : ℤ) * k + r) = positivePrimeWeight S (k + (ell : ℤ) * r) := by
  unfold positivePrimeWeight
  apply Finset.prod_congr rfl
  intro p hp
  simp only [crt_prime_divisibility N ell p (hinv p (hS hp)) k r]

lemma crt_padding_density (N ell : ℕ) (Q D : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → Prop)
    (hinv : ∀ p ∈ Q, (N : ZMod p) * (ell : ZMod p) = 1)
    (hD : ∀ q ∈ D, Squarefree q ∧ q.primeFactors ⊆ Q) (k r : ℤ) :
    paddingDensity D u eligible (actualPaddingVertex Q) ((N : ℤ) * k + r) =
      paddingDensity D u eligible (actualPaddingVertex Q) (k + (ell : ℤ) * r) := by
  unfold paddingDensity
  rw [crt_padding_vertex N ell Q hinv k r]
  congr 1
  apply Finset.sum_congr rfl
  intro q hq
  simp only [crt_squarefree_divisibility N ell q Q (hD q hq).1 (hD q hq).2 hinv k r]

lemma crt_integer_edge_keep (N ell : ℕ) (Q D : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → Prop)
    (L K : ℝ) (hinv : ∀ p ∈ Q, (N : ZMod p) * (ell : ZMod p) = 1)
    (hD : ∀ q ∈ D, Squarefree q ∧ q.primeFactors ⊆ Q) (k r : ℤ) :
    integerEdgeKeep D u eligible (actualPaddingVertex Q) L K (actualPaddingDegreeCut Q L) ((N : ℤ) * k + r) ↔
      integerEdgeKeep D u eligible (actualPaddingVertex Q) L K (actualPaddingDegreeCut Q L) (k + (ell : ℤ) * r) := by
  unfold integerEdgeKeep actualPaddingDegreeCut
  rw [crt_padding_density N ell Q D u eligible hinv hD k r, crt_padding_degree N ell Q hinv k r]

#print axioms crt_squarefree_divisibility
#print axioms crt_integer_edge_keep

end ReflectedLiouville
