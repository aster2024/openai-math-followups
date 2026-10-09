import ReflectedLiouville.CRTDirectedEdges

set_option autoImplicit false
open scoped Classical
open OAI.TwoPointCorrelations

namespace ReflectedLiouville

/-- Exact cancellation of both square-root vertex weights in a reflected
    test pairing; no equality of the endpoint weights is assumed. -/
theorem directed_edge_cancel_tests (D : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → Prop)
    (g center : ℤ → ℝ) (L K : ℝ) (extra : ℤ → Prop) (N d q : ℕ)
    (n m : ℤ) (F G : ℝ) (hn : g n ≠ 0) (hm : g m ≠ 0) :
    (g m * F) * directedIntegerEdge D u eligible g center L K extra N d q n m * (g n * G) =
      if q ∈ D ∧ m = n + ((N * q * d : ℕ) : ℤ) ∧ eligible q ∧ (q : ℤ) ∣ n ∧
        integerEdgeKeep D u eligible g L K extra n ∧ integerEdgeKeep D u eligible g L K extra m then
        L * u q * center n * F * G else 0 := by
  unfold directedIntegerEdge
  split_ifs
  · field_simp [hn, hm]
    <;> ring
  · ring

lemma centered_tuple_at_reflected_endpoint (N q d : ℕ) (n : ℤ) :
    centeredTuple d.primeFactors (n - ((N * q * d : ℕ) : ℤ)) = centeredTuple d.primeFactors n := by
  have hshift : ∀ p ∈ d.primeFactors, (p : ℤ) ∣ -((N * q * d : ℕ) : ℤ) := by
    intro p hp
    have hpd : p ∣ d := (Nat.mem_primeFactors.mp hp).2.1
    have hdv : p ∣ N * q * d := hpd.trans (dvd_mul_left d (N * q))
    exact dvd_neg.mpr (by exact_mod_cast hdv)
  simpa only [sub_eq_add_neg] using centeredTuple_add d.primeFactors n (-((N * q * d : ℕ) : ℤ)) hshift

lemma positive_weight_at_reflected_endpoint (N q d : ℕ) (n : ℤ) :
    positivePrimeWeight d.primeFactors (n - ((N * q * d : ℕ) : ℤ)) = positivePrimeWeight d.primeFactors n := by
  unfold positivePrimeWeight
  apply Finset.prod_congr rfl
  intro p hp
  have hpd : p ∣ d := (Nat.mem_primeFactors.mp hp).2.1
  have hdv : (p : ℤ) ∣ ((N * q * d : ℕ) : ℤ) := by
    exact_mod_cast hpd.trans (dvd_mul_left d (N * q))
  have hi : (p : ℤ) ∣ n - ((N * q * d : ℕ) : ℤ) ↔ (p : ℤ) ∣ n := dvd_sub_left hdv
  simp only [hi]

#print axioms directed_edge_cancel_tests
#print axioms positive_weight_at_reflected_endpoint

end ReflectedLiouville
