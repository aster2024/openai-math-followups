import ReflectedLiouville.PhysicalScalarPairing

set_option autoImplicit false
open scoped BigOperators Classical
open OAI.TwoPointCorrelations

namespace ReflectedLiouville

lemma directed_edge_forced_target (D : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → Prop)
    (g center : ℤ → ℝ) (L K : ℝ) (extra : ℤ → Prop) (N d q : ℕ) (x y : ℤ) :
    directedIntegerEdge D u eligible g center L K extra N d q y x =
      if y = x - ((N * q * d : ℕ) : ℤ) then
        directedIntegerEdge D u eligible g center L K extra N d q
          (x - ((N * q * d : ℕ) : ℤ)) x else 0 := by
  by_cases he : y = x - ((N * q * d : ℕ) : ℤ)
  · rw [he, ite_eq_left rfl]
  · have hstep : ¬x = y + ((N * q * d : ℕ) : ℤ) := by
      intro hh
      apply he
      rw [hh]
      ring
    simp only [directedIntegerEdge, hstep, and_false, false_and, ite_false, he]

lemma sum_forced_targets {V α : Type*} [Fintype V]
    (site : V → ℤ) (hinj : Function.Injective site) (Q : Finset α)
    (target : α → ℤ) (C : α → ℝ)
    (hcover : ∀ q ∈ Q, C q ≠ 0 → ∃ i, site i = target q) :
    (∑ i, ∑ q ∈ Q, if site i = target q then C q else 0) = ∑ q ∈ Q, C q := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hc : C q = 0
  · simp only [hc, ite_self, Finset.sum_const_zero]
  · obtain ⟨i₀, hi₀⟩ := hcover q hq hc
    have he (i : V) : site i = target q ↔ i = i₀ :=
      ⟨fun hh => hinj (hh.trans hi₀.symm), fun hh => hh ▸ hi₀⟩
    simp only [he, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- Collapse the graph target sum while retaining all physical endpoint
    masks. Coverage is needed only for the nonzero reflected atom. -/
theorem masked_directed_edge_pairing {V : Type*} [Fintype V]
    (site : V → ℤ) (hinj : Function.Injective site)
    (D : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → Prop)
    (g center : ℤ → ℝ) (L K : ℝ) (extra keep : ℤ → Prop)
    (N d : ℕ) (x : ℤ) (F : ℝ) (G : ℤ → ℝ)
    (hcover : ∀ q ∈ D,
      (if keep x ∧ keep (x - ((N * q * d : ℕ) : ℤ)) then
        F * directedIntegerEdge D u eligible g center L K extra N d q
          (x - ((N * q * d : ℕ) : ℤ)) x * G (x - ((N * q * d : ℕ) : ℤ)) else 0) ≠ 0 →
          ∃ i, site i = x - ((N * q * d : ℕ) : ℤ)) :
    (∑ i, if keep x ∧ keep (site i) then
      F * (∑ q ∈ D, directedIntegerEdge D u eligible g center L K extra N d q (site i) x) * G (site i) else 0) =
      ∑ q ∈ D, if keep x ∧ keep (x - ((N * q * d : ℕ) : ℤ)) then
        F * directedIntegerEdge D u eligible g center L K extra N d q
          (x - ((N * q * d : ℕ) : ℤ)) x * G (x - ((N * q * d : ℕ) : ℤ)) else 0 := by
  let C := fun q => if keep x ∧ keep (x - ((N * q * d : ℕ) : ℤ)) then
    F * directedIntegerEdge D u eligible g center L K extra N d q
      (x - ((N * q * d : ℕ) : ℤ)) x * G (x - ((N * q * d : ℕ) : ℤ)) else 0
  have hrow (i : V) :
      (if keep x ∧ keep (site i) then
        F * (∑ q ∈ D, directedIntegerEdge D u eligible g center L K extra N d q (site i) x) * G (site i) else 0) =
        ∑ q ∈ D, if site i = x - ((N * q * d : ℕ) : ℤ) then C q else 0 := by
    have hdist :
        (if keep x ∧ keep (site i) then
          ∑ q ∈ D, F * directedIntegerEdge D u eligible g center L K extra N d q (site i) x * G (site i) else 0) =
          ∑ q ∈ D, if keep x ∧ keep (site i) then
            F * directedIntegerEdge D u eligible g center L K extra N d q (site i) x * G (site i) else 0 := by
      by_cases hk : keep x ∧ keep (site i) <;> simp only [hk, and_self, ite_true, ite_false, Finset.sum_const_zero]
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [hdist]
    apply Finset.sum_congr rfl
    intro q hq
    by_cases he : site i = x - ((N * q * d : ℕ) : ℤ)
    · simp only [he, ite_true, C]
    · rw [directed_edge_forced_target]
      simp only [he, ite_false, mul_zero, zero_mul, ite_self]
  simp_rw [hrow]
  exact sum_forced_targets site hinj D _ C hcover

#print axioms masked_directed_edge_pairing
end ReflectedLiouville
