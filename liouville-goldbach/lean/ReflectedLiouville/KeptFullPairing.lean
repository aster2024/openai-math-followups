import ReflectedLiouville.TuplePairSum
import ReflectedLiouville.PhysicalFrameCover

set_option autoImplicit false
set_option maxHeartbeats 1500000
open scoped BigOperators Classical
open OAI.TwoPointCorrelations Finset

namespace ReflectedLiouville

/-- Exact full-bin pairing on a finite centered frame. All coverage and
    bin-window requirements are finite numerical conditions. -/
theorem kept_full_pairing {N J M MB B : ℕ}
    (data : ProhibitedPrimeFamily N J M) (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j k, k ≠ j → Disjoint (P j) (P k))
    (hUnion : univ.biUnion P = data.P)
    (hsub : data.pairs ⊆ primeTupleDivisors P ×ˢ boundedPaddingDivisors data.Q M)
    (L W η : ℝ) (j : ℤ) (U : ℝ) (hN : 0 < N)
    (hFrame : 2 * (B + 1) ≤ MB)
    (hSource : reflectionBinCutoff N η j / N ≤ (B : ℝ))
    (hTarget : U / N + 1 ≤ (B : ℝ))
    (hStep : ∀ dq ∈ data.pairs, reflectionPairBin η dq = j →
      (((N * dq.1 * dq.2 : ℕ) : ℤ) : ℝ) ≤ U) :
    let T := reflectionBinCutoff N η j
    let site := fun i : Fin MB => (i.val : ℤ) - (MB / 2 : ℕ)
    (∑ r : Fin N, inner ℂ
      (sourceTestVector data.Q T L (fun i => (N : ℤ) * site i + ((r.val + 1 : ℕ) : ℤ)))
      (physicalReflectionCompression data P site ((r.val + 1 : ℕ) : ℤ) L W
        (binPairEligible data.pairs η j)
        (targetTestVector data.Q U L (fun i => (N : ℤ) * site i + ((r.val + 1 : ℕ) : ℤ))))) =
      ((L * T * keptCenteredBinForm data L W η j : ℝ) : ℂ) := by
  dsimp only
  let T := reflectionBinCutoff N η j
  let site := fun i : Fin MB => (i.val : ℤ) - (MB / 2 : ℕ)
  let eligible := binPairEligible data.pairs η j
  let Q := boundedPaddingDivisors data.Q M
  let F := fun (d : (k : Fin J) → P k) (x : ℤ) =>
    ∑ q ∈ Q, if eligible (∏ k, (d k).val) q then
      L * keptReflectionAtom data L W eligible (∏ k, (d k).val, q) x else 0
  let physical := fun (r : Fin N) (i : Fin MB) => (N : ℤ) * site i + ((r.val + 1 : ℕ) : ℤ)
  have hT : 0 < T := by dsimp only [T]; unfold reflectionBinCutoff; positivity
  have hsite : Function.Injective site := by
    intro i k he
    apply Fin.ext
    dsimp only [site] at he
    omega
  have hphysical (r : Fin N) : Function.Injective (physical r) := by
    intro i k he
    apply hsite
    have hn : (N : ℤ) ≠ 0 := by exact_mod_cast hN.ne'
    exact mul_left_cancel₀ hn (add_right_cancel he)
  have hrow (r : Fin N) (d : (k : Fin J) → P k) (i : Fin MB) :
      (∑ k : Fin MB,
        if (actualPaddingDegree data.P (physical r i) : ℝ) ≤ 6 * W * J ∧
          (actualPaddingDegree data.P (physical r k) : ℝ) ≤ 6 * W * J ∧
          ¬ProhibitedSite N ⌊L ^ (1 / 10 : ℝ)⌋₊ (fun d q => (d,q) ∈ data.pairs) (physical r i) ∧
          ¬ProhibitedSite N ⌊L ^ (1 / 10 : ℝ)⌋₊ (fun d q => (d,q) ∈ data.pairs) (physical r k) then
          sourceTestValue data.Q T L (physical r i) *
            (∑ q ∈ Q, directedIntegerEdge Q actualPaddingCoefficient
              (eligible (∏ l, (d l).val)) (actualPaddingVertex data.Q)
              (centeredTuple (∏ l, (d l).val).primeFactors) L (Real.exp (4 * J))
              (actualPaddingDegreeCut data.Q L) N (∏ l, (d l).val) q (physical r k) (physical r i)) *
            targetTestValue data.Q U L (physical r k) else 0) =
        if 0 < physical r i ∧ (physical r i : ℝ) ≤ T then F d (physical r i) else 0 := by
    have hr : 1 ≤ ((r.val + 1 : ℕ) : ℤ) ∧ ((r.val + 1 : ℕ) : ℤ) ≤ (N : ℤ) := by
      exact_mod_cast (show 1 ≤ r.val + 1 ∧ r.val + 1 ≤ N by have := r.isLt; omega)
    have hc : ∀ q ∈ Q,
        targetTestValue data.Q U L (physical r i - ((N*q*(∏ l, (d l).val) : ℕ) : ℤ)) ≠ 0 →
          ∃ k, physical r k = physical r i - ((N*q*(∏ l, (d l).val) : ℕ) : ℤ) := by
      intro q hq hg
      exact physical_frame_target_cover N MB B hN _ hr U L data.Q hFrame hTarget
        (site i) (∏ l, (d l).val) q hg
    have hs : ∀ q ∈ Q, eligible (∏ l, (d l).val) q →
        (((N * (∏ l, (d l).val) * q : ℕ) : ℤ) : ℝ) ≤ U := by
      intro q hq he
      exact hStep _ he.1 he.2
    have he := kept_row_pairing data (physical r) (hphysical r) L W T U eligible
      (∏ l, (d l).val) (physical r i) hc hs
    apply Eq.trans _ he
    apply sum_congr rfl
    intro k hk
    have hgate : (reflectionCenterKeep data L W (physical r i) ∧
      reflectionCenterKeep data L W (physical r k)) ↔
      (actualPaddingDegree data.P (physical r i) : ℝ) ≤ 6 * W * J ∧
        (actualPaddingDegree data.P (physical r k) : ℝ) ≤ 6 * W * J ∧
        ¬ProhibitedSite N ⌊L ^ (1 / 10 : ℝ)⌋₊ (fun d q => (d,q) ∈ data.pairs) (physical r i) ∧
        ¬ProhibitedSite N ⌊L ^ (1 / 10 : ℝ)⌋₊ (fun d q => (d,q) ∈ data.pairs) (physical r k) := by
      unfold reflectionCenterKeep
      tauto
    simp only [hgate, Q]
  have hinner (r : Fin N) : inner ℂ
      (sourceTestVector data.Q T L (physical r))
      (physicalReflectionCompression data P site ((r.val + 1 : ℕ) : ℤ) L W eligible
        (targetTestVector data.Q U L (physical r))) =
      ((∑ d : (k : Fin J) → P k, ∑ i : Fin MB,
        if 0 < physical r i ∧ (physical r i : ℝ) ≤ T then F d (physical r i) else 0 : ℝ) : ℂ) := by
    rw [physical_scalar_pairing data P hprime hdisjoint hUnion site _ L W T U eligible]
    congr 1
    apply sum_congr rfl
    intro d hd
    apply sum_congr rfl
    intro i hi
    exact hrow r d i
  have hprefix (d : (k : Fin J) → P k) :
      (∑ r : Fin N, ∑ i : Fin MB,
        if 0 < physical r i ∧ (physical r i : ℝ) ≤ T then F d (physical r i) else 0) =
        ∑ n ∈ Icc 1 ⌊T⌋₊, F d (n : ℤ) := by
    simpa only [physical, Int.cast_add, Int.cast_mul, Int.cast_natCast] using
      physical_positive_prefix_sum N hN site hsite T hT.le (F d)
        (physical_frame_source_cover N MB B hN T hFrame hSource)
  let Ib := data.pairs.filter (fun dq => reflectionPairBin η dq = j)
  have hIb : Ib ⊆ primeTupleDivisors P ×ˢ Q := fun dq hdq => hsub (mem_filter.mp hdq).1
  have hpair (n : ℕ) : (∑ d : (k : Fin J) → P k, F d (n : ℤ)) =
      ∑ dq ∈ Ib, L * keptReflectionAtom data L W eligible dq (n : ℤ) := by
    have he (d q : ℕ) : eligible d q ↔ (d,q) ∈ Ib := by simp only [eligible, binPairEligible, Ib, mem_filter]
    dsimp only [F]
    simp_rw [he]
    convert tuple_pair_sum P hprime hdisjoint Q Ib hIb
      (fun dq => L * keptReflectionAtom data L W eligible dq (n : ℤ)) using 1
  change (∑ r : Fin N, inner ℂ (sourceTestVector data.Q T L (physical r))
    (physicalReflectionCompression data P site ((r.val + 1 : ℕ) : ℤ) L W eligible
      (targetTestVector data.Q U L (physical r)))) = _
  simp_rw [hinner]
  rw [← Complex.ofReal_sum]
  congr 1
  rw [sum_comm]
  simp_rw [hprefix]
  rw [sum_comm]
  simp_rw [hpair]
  rw [sum_comm]
  change (∑ dq ∈ Ib, ∑ n ∈ Icc 1 ⌊T⌋₊, L * keptReflectionAtom data L W eligible dq (n : ℤ)) =
    L * T * ((∑ dq ∈ Ib, ∑ n ∈ Icc 1 ⌊T⌋₊, keptReflectionAtom data L W eligible dq (n : ℤ)) / T)
  simp_rw [← mul_sum]
  field_simp [hT.ne']

#print axioms kept_full_pairing
end ReflectedLiouville
