import ReflectedLiouville.CRTFactors

set_option autoImplicit false
open scoped BigOperators Classical
open OAI.TwoPointCorrelations

namespace ReflectedLiouville

lemma crt_edge_displacement (N ell d q : ℕ) (hN : 0 < N) (k t r : ℤ) :
    (N : ℤ) * t + r = (N : ℤ) * k + r + ((N * q * d : ℕ) : ℤ) ↔
      t + (ell : ℤ) * r = k + (ell : ℤ) * r + ((1 * q * d : ℕ) : ℤ) := by
  have hN0 : (N : ℤ) ≠ 0 := by exact_mod_cast hN.ne'
  have hid : (N : ℤ) * k + r + ((N * q * d : ℕ) : ℤ) =
      (N : ℤ) * (k + ((q * d : ℕ) : ℤ)) + r := by push_cast; ring
  have hphysical : (N : ℤ) * t + r = (N : ℤ) * k + r + ((N * q * d : ℕ) : ℤ) ↔
      t = k + ((q * d : ℕ) : ℤ) := by
    rw [hid]
    constructor
    · intro h
      exact mul_left_cancel₀ hN0 (add_right_cancel h)
    · intro h
      rw [h]
  rw [hphysical, Nat.one_mul]
  constructor <;> intro h <;> omega

lemma crt_directed_integer_edge (N ell d q : ℕ) (hN : 0 < N)
    (P Q D : Finset ℕ) (hQP : Q ⊆ P) (hcenter : d.primeFactors ⊆ P)
    (hinv : ∀ p ∈ P, (N : ZMod p) * (ell : ZMod p) = 1)
    (hD : ∀ q ∈ D, Squarefree q ∧ q.primeFactors ⊆ Q)
    (u : ℕ → ℝ) (eligible : ℕ → Prop) (L K : ℝ) (k t r : ℤ) :
    directedIntegerEdge D u eligible (actualPaddingVertex Q) (centeredTuple d.primeFactors) L K
      (actualPaddingDegreeCut Q L) N d q ((N : ℤ) * k + r) ((N : ℤ) * t + r) =
    directedIntegerEdge D u eligible (actualPaddingVertex Q) (centeredTuple d.primeFactors) L K
      (actualPaddingDegreeCut Q L) 1 d q (k + (ell : ℤ) * r) (t + (ell : ℤ) * r) := by
  by_cases hq : q ∈ D
  · have hQinv : ∀ p ∈ Q, (N : ZMod p) * (ell : ZMod p) = 1 := fun p hp => hinv p (hQP hp)
    have hstep := crt_edge_displacement N ell d q hN k t r
    have hdiv := crt_squarefree_divisibility N ell q Q (hD q hq).1 (hD q hq).2 hQinv k r
    have hkeepK := crt_integer_edge_keep N ell Q D u eligible L K hQinv hD k r
    have hkeepT := crt_integer_edge_keep N ell Q D u eligible L K hQinv hD t r
    have hcenterK := crt_centered_tuple N ell P d.primeFactors hcenter hinv k r
    have hgK := crt_padding_vertex N ell Q hQinv k r
    have hgT := crt_padding_vertex N ell Q hQinv t r
    unfold directedIntegerEdge
    simp only [hq, true_and, hstep, hdiv, hkeepK, hkeepT, hcenterK, hgK, hgT]
  · unfold directedIntegerEdge
    simp only [hq, false_and, ite_false]

theorem crt_integer_edge_matrix {ι : Type*} [Fintype ι]
    (N ell d : ℕ) (hN : 0 < N) (site : ι → ℤ) (r : ℤ)
    (P Q D : Finset ℕ) (hQP : Q ⊆ P) (hcenter : d.primeFactors ⊆ P)
    (hinv : ∀ p ∈ P, (N : ZMod p) * (ell : ZMod p) = 1)
    (hD : ∀ q ∈ D, Squarefree q ∧ q.primeFactors ⊆ Q)
    (u : ℕ → ℝ) (eligible : ℕ → Prop) (L K : ℝ) :
    integerEdgeMatrix (fun i => (N : ℤ) * site i + r) D u eligible (actualPaddingVertex Q)
      (centeredTuple d.primeFactors) L K (actualPaddingDegreeCut Q L) N d =
    integerEdgeMatrix (fun i => site i + (ell : ℤ) * r) D u eligible (actualPaddingVertex Q)
      (centeredTuple d.primeFactors) L K (actualPaddingDegreeCut Q L) 1 d := by
  funext i j
  unfold integerEdgeMatrix
  apply Finset.sum_congr rfl
  intro q hq
  rw [crt_directed_integer_edge N ell d q hN P Q D hQP hcenter hinv hD u eligible L K,
    crt_directed_integer_edge N ell d q hN P Q D hQP hcenter hinv hD u eligible L K]

#print axioms crt_integer_edge_matrix

end ReflectedLiouville
