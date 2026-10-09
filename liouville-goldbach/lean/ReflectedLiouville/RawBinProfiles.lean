import ReflectedLiouville.ReflectedBinProfiles

set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped BigOperators Classical
open OAI.TwoPointCorrelations Finset

namespace ReflectedLiouville

lemma reflected_divisor_atom_prefix (N a B : ℕ) :
    (∑ n ∈ Icc 1 B, natDivisibilityIndicator a n * liouville n * liouville (N * a - n)) =
      (dilatedReflectedSum N a B : ℂ) := by
  rw [dilatedReflectedSum_cast, sum_filter]
  apply sum_congr rfl
  intro n hn
  have he : N * a = a * N := by ring
  by_cases hd : a ∣ n <;> simp only [natDivisibilityIndicator, hd, ite_true, ite_false,
    one_mul, zero_mul, he]

lemma raw_bin_profile_identity {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j k, k ≠ j → Disjoint (P j) (P k))
    (Q : Finset ℕ) (I : Finset (ℕ × ℕ)) (hsub : I ⊆ primeTupleDivisors P ×ˢ Q)
    (N : ℕ) (η : ℝ) (j : ℤ) :
    (∑ q ∈ Q, (actualPaddingCoefficient q : ℂ) *
      (positivePrefix (reflectedTuplePartialProfile P ∅ q N (binPairEligible I η j))
        ⌊reflectionBinCutoff N η j⌋₊ / (reflectionBinCutoff N η j : ℂ))) =
      (rawBinForm I N η j : ℂ) := by
  let Ib := I.filter (fun dq => reflectionPairBin η dq = j)
  let F := fun (dq : ℕ × ℕ) (n : ℕ) => (actualPaddingCoefficient dq.2 : ℂ) *
    natDivisibilityIndicator (dq.1 * dq.2) n * liouville n * liouville (N * (dq.1 * dq.2) - n)
  have hIb : Ib ⊆ primeTupleDivisors P ×ˢ Q := fun dq hdq => hsub (mem_filter.mp hdq).1
  have he (d q : ℕ) : binPairEligible I η j d q ↔ (d,q) ∈ Ib := by
    simp only [binPairEligible, Ib, mem_filter]
  have hpoint (n : ℕ) :
      (∑ q ∈ Q, (actualPaddingCoefficient q : ℂ) *
        reflectedTuplePartialProfile P ∅ q N (binPairEligible I η j) n) = ∑ dq ∈ Ib, F dq n := by
    simp only [reflectedTuplePartialProfile_empty, mul_sum]
    rw [sum_comm]
    apply Eq.trans _ (tuple_pair_sum P hprime hdisjoint Q Ib hIb (fun dq => F dq n))
    apply sum_congr rfl
    intro x hx
    apply sum_congr rfl
    intro q hq
    rw [he]
    have hm : q * ∏ k, (x k).val = (∏ k, (x k).val) * q := by ring
    split_ifs
    · simp only [F, hm]
      ring
    · simp only [mul_zero]
  have hnum : (∑ q ∈ Q, (actualPaddingCoefficient q : ℂ) *
      positivePrefix (reflectedTuplePartialProfile P ∅ q N (binPairEligible I η j))
        ⌊reflectionBinCutoff N η j⌋₊) =
      ∑ dq ∈ Ib, (actualPaddingCoefficient dq.2 : ℂ) *
        (dilatedReflectedSum N (dq.1 * dq.2) ⌊reflectionBinCutoff N η j⌋₊ : ℂ) := by
    simp only [positivePrefix_eq_Icc, mul_sum]
    rw [sum_comm]
    simp_rw [hpoint]
    rw [sum_comm]
    apply sum_congr rfl
    intro dq hdq
    dsimp only [F]
    rw [← reflected_divisor_atom_prefix, mul_sum]
    apply sum_congr rfl
    intro n hn
    ring
  have hdiv : (∑ q ∈ Q, (actualPaddingCoefficient q : ℂ) *
      (positivePrefix (reflectedTuplePartialProfile P ∅ q N (binPairEligible I η j))
        ⌊reflectionBinCutoff N η j⌋₊ / (reflectionBinCutoff N η j : ℂ))) =
      (∑ q ∈ Q, (actualPaddingCoefficient q : ℂ) *
        positivePrefix (reflectedTuplePartialProfile P ∅ q N (binPairEligible I η j))
          ⌊reflectionBinCutoff N η j⌋₊) / (reflectionBinCutoff N η j : ℂ) := by
    rw [sum_div]
    apply sum_congr rfl
    intro q hq
    ring
  rw [hdiv, hnum]
  simp only [rawBinForm, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_div]
  rw [sum_div]
  apply sum_congr rfl
  intro dq hdq
  ring

lemma centering_bin_profile_difference {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j k, k ≠ j → Disjoint (P j) (P k))
    (Q : Finset ℕ) (I : Finset (ℕ × ℕ)) (hsub : I ⊆ primeTupleDivisors P ×ˢ Q)
    (N : ℕ) (η : ℝ) (j : ℤ) :
    |centeredBinForm I N η j - rawBinForm I N η j| =
      ‖∑ q ∈ Q, (actualPaddingCoefficient q : ℂ) *
        ((positivePrefix (reflectedTupleCenteredProfile P q N (binPairEligible I η j))
            ⌊reflectionBinCutoff N η j⌋₊ -
          positivePrefix (reflectedTuplePartialProfile P ∅ q N (binPairEligible I η j))
            ⌊reflectionBinCutoff N η j⌋₊) / (reflectionBinCutoff N η j : ℂ))‖ := by
  simp only [sub_div, mul_sub, sum_sub_distrib]
  rw [centered_bin_profile_identity P hprime hdisjoint Q I hsub,
    raw_bin_profile_identity P hprime hdisjoint Q I hsub, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs]

#print axioms centering_bin_profile_difference
end ReflectedLiouville
