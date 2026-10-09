import ReflectedLiouville.ReflectedAtomCasts
import ReflectedLiouville.ReflectedCenteringBin
import ReflectedLiouville.TuplePairSum
import ReflectedLiouville.ComplexDilation

set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped BigOperators Classical
open OAI.TwoPointCorrelations Finset

namespace ReflectedLiouville

lemma reflectedTuplePartialProfile_empty {J : ℕ} (P : Fin J → Finset ℕ)
    (q N : ℕ) (eligible : ℕ → ℕ → Prop) (n : ℕ) :
    reflectedTuplePartialProfile P ∅ q N eligible n =
      ∑ x : (j : Fin J) → P j, if eligible (∏ j, (x j).val) q then
        natDivisibilityIndicator (q * ∏ j, (x j).val) n *
          (liouville n * liouville (N * (q * ∏ j, (x j).val) - n)) else 0 := by
  unfold reflectedTuplePartialProfile
  apply sum_congr rfl
  intro x hx
  have he : (∏ j : {j // j ∉ (∅ : Finset (Fin J))}, (x j).val) =
      ∏ j, (x j).val := (prod_subtype univ (by simp) (fun j => (x j).val)).symm
  simp only [Fintype.prod_empty, Nat.cast_one, div_one, one_mul, he]

lemma centered_bin_profile_identity {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j k, k ≠ j → Disjoint (P j) (P k))
    (Q : Finset ℕ) (I : Finset (ℕ × ℕ)) (hsub : I ⊆ primeTupleDivisors P ×ˢ Q)
    (N : ℕ) (η : ℝ) (j : ℤ) :
    (∑ q ∈ Q, (actualPaddingCoefficient q : ℂ) *
      (positivePrefix (reflectedTupleCenteredProfile P q N (binPairEligible I η j))
        ⌊reflectionBinCutoff N η j⌋₊ / (reflectionBinCutoff N η j : ℂ))) =
      (centeredBinForm I N η j : ℂ) := by
  let Ib := I.filter (fun dq => reflectionPairBin η dq = j)
  have hIb : Ib ⊆ primeTupleDivisors P ×ˢ Q := fun dq hdq => hsub (mem_filter.mp hdq).1
  have he (d q : ℕ) : binPairEligible I η j d q ↔ (d,q) ∈ Ib := by
    simp only [binPairEligible, Ib, mem_filter]
  have hpoint (n : ℕ) :
      (∑ q ∈ Q, (actualPaddingCoefficient q : ℂ) *
        reflectedTupleCenteredProfile P q N (binPairEligible I η j) n) =
        ∑ dq ∈ Ib, (centeredReflectionAtom N dq (n : ℤ) : ℂ) := by
    simp only [reflectedTupleCenteredProfile, mul_sum]
    rw [sum_comm]
    have ht := tuple_pair_sum P hprime hdisjoint Q Ib hIb
      (fun dq => (centeredReflectionAtom N dq (n : ℤ) : ℂ))
    apply Eq.trans _ ht
    apply sum_congr rfl
    intro x hx
    apply sum_congr rfl
    intro q hq
    rw [he]
    split_ifs
    · rw [centeredReflectionAtom_cast_nat]
      ring
    · simp only [mul_zero]
  have hnum : (∑ q ∈ Q, (actualPaddingCoefficient q : ℂ) *
      positivePrefix (reflectedTupleCenteredProfile P q N (binPairEligible I η j))
        ⌊reflectionBinCutoff N η j⌋₊) =
      ∑ dq ∈ Ib, ∑ n ∈ Icc 1 ⌊reflectionBinCutoff N η j⌋₊,
        (centeredReflectionAtom N dq (n : ℤ) : ℂ) := by
    simp only [positivePrefix_eq_Icc, mul_sum]
    rw [sum_comm]
    simp_rw [hpoint]
    exact sum_comm
  have hdiv : (∑ q ∈ Q, (actualPaddingCoefficient q : ℂ) *
      (positivePrefix (reflectedTupleCenteredProfile P q N (binPairEligible I η j))
        ⌊reflectionBinCutoff N η j⌋₊ / (reflectionBinCutoff N η j : ℂ))) =
      (∑ q ∈ Q, (actualPaddingCoefficient q : ℂ) *
        positivePrefix (reflectedTupleCenteredProfile P q N (binPairEligible I η j))
          ⌊reflectionBinCutoff N η j⌋₊) / (reflectionBinCutoff N η j : ℂ) := by
    rw [sum_div]
    apply sum_congr rfl
    intro q hq
    ring
  rw [hdiv, hnum]
  simp only [centeredBinForm, Complex.ofReal_div, Complex.ofReal_sum]
  rfl

#print axioms centered_bin_profile_identity
end ReflectedLiouville
