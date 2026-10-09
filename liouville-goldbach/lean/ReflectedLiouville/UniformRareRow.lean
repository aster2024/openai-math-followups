import ReflectedLiouville.ReflectionProhibitedDensity
import OAI.NumberTheory.TwoPoint.Bounds.ActualRareRow
import OAI.NumberTheory.TwoPoint.Bounds.RareRowSum
import OAI.NumberTheory.TwoPoint.Bounds.PositiveCostPeriodicity

set_option autoImplicit false
open Filter
open scoped BigOperators Classical
open OAI.TwoPointCorrelations

namespace ReflectedLiouville

lemma finiteLaw_average_finset_sum {ι Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (I : Finset ι) (F : ι → Ω → ℝ) :
    μ.average (fun x => ∑ i ∈ I, F i x) = ∑ i ∈ I, μ.average (F i) := by
  unfold FiniteLaw.average
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]

/-- A uniform rare-row estimate from the numerical pool range. All families,
    bands and bad events follow the L threshold, including changing exclusions. -/
theorem uniform_rare_row_bound (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ (h J M B : ℕ) (data : ProhibitedPrimeFamily h J M)
      (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
      (P : Fin J → Finset ℕ) (W α : ℝ),
      ReflectionPoolRange data P L W α → 10 ≤ W → 1 ≤ L →
      ∀ (site : ℤ) (bad : (↥(data.P ∪ data.Q) → Fin B) → Prop),
        (data.residueLaw B hB).probability bad ≤ Real.exp (-(1 / 2 : ℝ) * L ^ (199 / 200 : ℝ)) →
        ∀ A : ℝ, 0 ≤ A → A ≤ Real.exp (C * Real.log L) →
          A * (data.residueLaw B hB).average (fun x =>
            primeRowMajorant P data.Q (data.residueOrigin x + site) * if bad x then 1 else 0) ≤
              Real.exp (-L ^ (9 / 10 : ℝ)) := by
  filter_upwards [eventually_rare_row_decay C hC] with L hdecay
  intro h J M B data hB P W α hrange hW hL site bad hbad A hA hAcap
  have hsq := data.prime_row_rare_square_bound hB P hrange.bandSubset hrange.bandDisjoint site
    L W hL hW hrange.paddingLog hrange.bandsUpper hrange.countW bad hbad
  apply hdecay A _ hA _ hAcap hsq
  exact (data.residueLaw B hB).average_nonneg (fun x =>
    mul_nonneg (primeRowMajorant_nonneg P data.Q _) (by split_ifs <;> norm_num))

/-- Every pair may have its own target shift. The exact periodicity theorem
    translates each positive atom before the row estimate is applied. -/
lemma prohibited_atom_sum_le_row {h J M B : ℕ}
    (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (P : Fin J → Finset ℕ) (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (hsub : ∀ j, P j ⊆ data.P)
    (T : Finset ℕ) (hT : T ⊆ primeTupleDivisors P)
    (padding : ℕ → Finset ℕ) (hpadding : ∀ d ∈ T, padding d ⊆ retainedPrimeDivisors data.Q)
    (s : ℕ) (site : ℕ → ℕ → ℤ) :
    (∑ d ∈ T, ∑ q ∈ padding d, (data.residueLaw B hB).average (fun x =>
      actualPaddingCoefficient q * positivePrimeWeight d.primeFactors (data.residueOrigin x + site d q) *
        if (q : ℤ) ∣ data.residueOrigin x + site d q ∧
          ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) (data.residueOrigin x + site d q)
        then 1 else 0)) ≤
      (data.residueLaw B hB).average (fun x => primeRowMajorant P data.Q (data.residueOrigin x) *
        if data.deletedEvent s B x then 1 else 0) := by
  have hpf (d : ℕ) (hd : d ∈ T) : d.primeFactors ⊆ data.P ∪ data.Q := by
    have ht := primeTupleDivisors_arithmetic P hprime hdisjoint (hT hd)
    intro p hp
    obtain ⟨j, hj⟩ := mem_primeTuplePool.mp (ht.2.2 hp)
    exact Finset.mem_union_left _ (hsub j hj)
  have hpoint (d : ℕ) (hd : d ∈ T) (q : ℕ) (hq : q ∈ padding d) :=
    data.prohibited_cost_average_translate hB d.primeFactors (hpf d hd) s q (hpadding d hd hq) (site d q)
  let F := fun (d q : ℕ) (x : ↥(data.P ∪ data.Q) → Fin B) =>
    actualPaddingCoefficient q * positivePrimeWeight d.primeFactors (data.residueOrigin x) *
      if (q : ℤ) ∣ data.residueOrigin x ∧
        ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) (data.residueOrigin x) then (1 : ℝ) else 0
  calc
    _ = ∑ d ∈ T, ∑ q ∈ padding d, (data.residueLaw B hB).average (F d q) := by
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro q hq
      exact hpoint d hd q hq
    _ = (data.residueLaw B hB).average (fun x => ∑ d ∈ T, ∑ q ∈ padding d, F d q x) := by
      symm
      rw [finiteLaw_average_finset_sum]
      apply Finset.sum_congr rfl
      intro d hd
      exact finiteLaw_average_finset_sum _ _ _
    _ ≤ _ := by
      apply (data.residueLaw B hB).average_mono
      intro x
      have hrow := positive_rare_row_bound P hprime hdisjoint data.Q T data.primeQ hT padding hpadding
        (data.residueOrigin x) (ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) (data.residueOrigin x))
      have heq := data.deletedEvent_iff s B x (data.residueOrigin x) (data.residueOrigin_spec x)
      simpa only [F, heq] using hrow

#print axioms uniform_rare_row_bound
#print axioms prohibited_atom_sum_le_row

end ReflectedLiouville
