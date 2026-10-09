import ReflectedLiouville.ExplicitShiftedComparisons
import ReflectedLiouville.ReflectedPaddingInteger
import ReflectedLiouville.ReflectedRareInteger

set_option autoImplicit false
set_option maxHeartbeats 1500000
open OAI.TwoPointCorrelations Finset Filter
open scoped BigOperators Classical
namespace ReflectedLiouville

theorem explicit_reflected_shifted_padding_deletion
    :
    ∀ a₀ : ℝ, 1 ≤ a₀ →
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (N₀ : ℕ) [NeZero N₀], Real.exp 2 ≤ (N₀ : ℝ) → Real.log (N₀ : ℝ) ≤ L ^ a₀ →
      ∀ (h J M B : ℕ) (data : ProhibitedPrimeFamily h J M),
      data.Q = paddingPrimeSupply N₀.primeFactors L →
      ∀ (_hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B),
      (data.P ∪ data.Q).Nonempty → (B : ℝ) ≤ Real.exp L →
      ∀ (P : Fin J → Finset ℕ), primeTuplePool P = data.P →
      (∀ j, ∀ p ∈ P j, p.Prime) →
      (∀ j l, l ≠ j → Disjoint (P j) (P l)) → (J : ℝ) ≤ L ^ 2 →
      ∀ (D : Finset ℕ), D ⊆ primeTupleDivisors P →
      ∀ (Q : Finset ℕ), Q ⊆ retainedPrimeDivisors data.Q →
      (∀ q ∈ Q, (q.primeFactors.card : ℝ) ≤ 100 * Real.log L) →
      ∀ (bins : Finset ℤ) (η K : ℝ) (c : ℕ → ℝ), 0 < η → η ≤ 1 → 0 < K →
      ∀ (site : ℤ → ℕ → ℕ → ℤ) (a N : ℤ → ℕ),
      (∀ j ∈ bins, Real.exp (L ^ (289578 : ℕ) / 2) ≤ (N j : ℝ)) →
      (∑ j ∈ bins, ∑ d ∈ D, ∑ q ∈ Q, uniformAverage (fun x : Fin (N j) =>
        paddingRejectionAtom data.Q d.primeFactors Q (actualPaddingBin η (c d) j) L K q
          ((a j + x.val : ℤ) + site j d q))) / paddingTiltNormalizer data.Q ≤
        (2 : ℝ) ^ J * (∏ j, primeHarmonicMass (P j)) * (C * (Real.log L)^(10 : ℕ) / K + L ^ (-90 : ℝ)) +
          (2 * bins.card * D.card * Q.card * Real.exp (-(L ^ 9))) /
            paddingTiltNormalizer data.Q := by
  have hc := explicit_shifted_padding_comparison
  intro a₀ ha₀
  obtain ⟨C, hC, hm⟩ := padding_holes_tuple_sum a₀ ha₀
  refine ⟨C, hC, ?_⟩
  filter_upwards [hc, hm, eventually_ge_atTop (1 : ℝ)] with L hc hm hL
  intro N₀ inst hN₀ hN₀log h J M B data hQ hB hpool hBL P hPeq hprime hdisjoint hJ D hD Q hQsub hqdegree
    bins η K c hη hηone hK site a N hN
  have hd (d : ℕ) (hd : d ∈ D) := primeTupleDivisors_arithmetic P hprime hdisjoint (hD hd)
  have he := hc h J M B data hB hpool hBL D
    (fun d hmem => ((hd d hmem).2.2.trans_eq hPeq).trans subset_union_left)
    (fun d hmem => by simpa only [(hd d hmem).2.1] using hJ)
    Q hQsub hqdegree bins η K c site a N hN
  have he' := (abs_le.mp he).2
  have hm' := hm N₀ hN₀ hN₀log h J M B data hQ hB D (fun _ => Q)
    (fun _ => bins) η K c (fun _ => 0)
    (fun d hdmem => ⟨(hd d hdmem).1,(hd d hdmem).2.1,(hd d hdmem).2.2.trans_eq hPeq⟩)
    (fun _ _ => hQsub) hη hηone hK
  simp only [add_zero] at hm'
  have hmass : (∑ d ∈ D, 1 / (d : ℝ)) ≤ ∏ j, primeHarmonicMass (P j) := by
    apply (sum_le_sum_of_subset_of_nonneg hD (fun d _ _ => by positivity)).trans_eq
    simpa only [primeHarmonicMass_eq_sum] using primeTupleDivisors_mass P hprime hdisjoint
  have hsmall : 0 ≤ C * (Real.log L)^(10 : ℕ) / K + L ^ (-90 : ℝ) := by positivity
  have hm'' : (data.residueLaw B hB).average (fun x => ∑ d ∈ D,
      positivePrimeWeight d.primeFactors (data.residueOrigin x) *
        paddingRejectedMass data.Q Q bins η (c d) L K (data.residueOrigin x)) ≤
      paddingTiltNormalizer data.Q * (∏ j, primeHarmonicMass (P j)) * (2 : ℝ)^J *
        (C * (Real.log L)^(10 : ℕ) / K + L ^ (-90 : ℝ)) := by
    rw [(data.residueLaw B hB).average_finset_sum]
    apply hm'.trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmass (paddingTiltNormalizer_pos data.Q).le) (by positivity)) hsmall
  have hS := paddingTiltNormalizer_pos data.Q
  have hx := (div_le_div_iff_of_pos_right hS).mpr he'
  rw [sub_div] at hx
  have hmNorm : (data.residueLaw B hB).average (fun x => ∑ d ∈ D,
      positivePrimeWeight d.primeFactors (data.residueOrigin x) *
        paddingRejectedMass data.Q Q bins η (c d) L K (data.residueOrigin x)) / paddingTiltNormalizer data.Q ≤
      (2 : ℝ)^J * (∏ j, primeHarmonicMass (P j)) *
        (C * (Real.log L)^(10 : ℕ) / K + L ^ (-90 : ℝ)) := by
    apply (div_le_iff₀ hS).mpr
    convert hm'' using 1 <;> ring
  linarith only [hx,hmNorm]

theorem explicit_reflected_variable_rare_integer :
    ∀ (a W δ C : ℝ) (hW : 10 ≤ W) (hδ : 0 < δ) (hδsmall : δ ≤ 1/200) (hC : 0 ≤ C),
      ∀ᶠ L : ℝ in atTop,
      ∀ (N₀ : ℕ) [NeZero N₀], Real.log (N₀ : ℝ) ≤ L ^ a →
      ∀ (hL : 1 ≤ L) (η : ℝ), 0 < η → η ≤ 1 →
        let J := reflectionBandCount W δ L
        let data := reflectionPrimeFamily N₀ W δ L η hL (by linarith)
        let P := centeredPrimeBands N₀.primeFactors (L ^ (1-δ)) W J
        ∀ (D : Finset ℕ) (padding : ℤ → ℕ → Finset ℕ) (bins : Finset ℤ),
          D ⊆ primeTupleDivisors P →
          (∀ j ∈ bins, ∀ d ∈ D, padding j d ⊆ boundedPaddingDivisors data.Q ⌊100*Real.log L⌋₊) →
          (∀ j ∈ bins, ∀ d ∈ D, ∀ q ∈ padding j d, (d,q) ∈ data.pairs) →
          (bins.card : ℝ) ≤ Real.exp (C*Real.log L) →
          ∀ (site : ℤ → ℕ → ℕ → ℤ) (b U : ℤ → ℕ),
            (∀ j ∈ bins, Real.exp (L ^ (144789 : ℕ) / 2) ≤ (U j : ℝ)) →
            (∑ j ∈ bins, ∑ d ∈ D, ∑ q ∈ padding j d,
              uniformAverage (fun x : Fin (U j) => actualPaddingCoefficient q *
                positivePrimeWeight d.primeFactors ((b j+x.val : ℤ)+site j d q) *
                if (q : ℤ) ∣ (b j+x.val : ℤ)+site j d q ∧
                  ProhibitedSite N₀ ⌊L ^ (1/10 : ℝ)⌋₊ (fun d q => (d,q) ∈ data.pairs)
                    ((b j+x.val : ℤ)+site j d q) then 1 else 0)) ≤
              Real.exp (-L ^ (9/10 : ℝ)) + bins.card * data.pairs.card * Real.exp (-(L ^ 9)) := by
  have hcmp := explicit_shifted_prohibited_row_comparison
  intro a W δ C hW hδ hδsmall hC
  filter_upwards [hcmp,prohibited_deletion_cost a W δ C hW hδ hδsmall hC,
    eventually_reflection_pool_range a W δ (by linarith) hδ (by linarith),
    eventually_ge_atTop (101 : ℝ)] with L hcmp hmodel hpool hLbig
  intro N₀ inst hNlog hL η hη hηone
  dsimp only
  let J := reflectionBandCount W δ L
  let M := ⌊100*Real.log L⌋₊
  let data := reflectionPrimeFamily N₀ W δ L η hL (by linarith : 0 ≤ W)
  let P := centeredPrimeBands N₀.primeFactors (L ^ (1-δ)) W J
  let B := ⌊Real.exp L⌋₊
  have hrange := hpool N₀ hNlog hL η
  have hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B := hrange.residueBound
  let μ := data.residueLaw B hB
  have hnonempty : (data.P ∪ data.Q).Nonempty := by
    have hp : data.P.Nonempty := by
      by_contra hn
      have he := not_nonempty_iff_eq_empty.mp hn
      have hh := hrange.centerLower
      rw [he] at hh
      norm_num [primeHarmonicMass] at hh
    exact hp.mono subset_union_left
  have hBL : (B : ℝ) ≤ Real.exp L := Nat.floor_le (Real.exp_pos _).le
  have hLog : Real.log L ≤ L := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have hcap : ((J+M : ℕ) : ℝ) ≤ L^2 := hrange.slots.trans (by nlinarith only [hLog,hLbig])
  have hJcap : (J : ℝ) ≤ ((J+M : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right J M
  have hJ : (J : ℝ) ≤ L^2 := hJcap.trans hcap
  have hs : (⌊L ^ (1/10 : ℝ)⌋₊ : ℝ) ≤ L :=
    (Nat.floor_le (Real.rpow_nonneg (by linarith) _)).trans
      (by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hL (by norm_num : (1/10 : ℝ) ≤ 1))
  have hpairs := (reflection_family_support N₀ W δ L η hL (by linarith) hδ.le hη hηone).2
  intro D padding bins hD hpadding hMembership hbins site b U hU
  have hd (d : ℕ) (hd : d ∈ D) := primeTupleDivisors_arithmetic P hrange.bandPrimes hrange.bandDisjoint (hD hd)
  have hP : primeTuplePool P = data.P := rfl
  have hsupport (d : ℕ) (hdmem : d ∈ D) : d.primeFactors ⊆ data.P ∪ data.Q :=
    ((hd d hdmem).2.2.trans_eq hP).trans subset_union_left
  have hcard (d : ℕ) (hdmem : d ∈ D) : (d.primeFactors.card : ℝ) ≤ L^2 := by rw [(hd d hdmem).2.1]; exact hJ
  have hret (j : ℤ) (hj : j ∈ bins) (d : ℕ) (hdmem : d ∈ D) : padding j d ⊆ retainedPrimeDivisors data.Q :=
    (hpadding j hj d hdmem).trans (filter_subset _ _)
  have hdegree (j : ℤ) (hj : j ∈ bins) (d : ℕ) (hdmem : d ∈ D) (q : ℕ) (hq : q ∈ padding j d) :
      (q.primeFactors.card : ℝ) ≤ 100*Real.log L := by
    have hh := (mem_filter.mp (hpadding j hj d hdmem hq)).2
    exact (by exact_mod_cast hh : (q.primeFactors.card : ℝ) ≤ M).trans hrange.paddingDegree
  let model := fun j => μ.average (fun x => prohibitedPositiveRow data ⌊L ^ (1/10 : ℝ)⌋₊ D (padding j) (data.residueOrigin x))
  let cost := fun j => ∑ d ∈ D, ∑ q ∈ padding j d,
    uniformAverage (fun x : Fin (U j) => actualPaddingCoefficient q *
      positivePrimeWeight d.primeFactors ((b j+x.val : ℤ)+site j d q) *
      if (q : ℤ) ∣ (b j+x.val : ℤ)+site j d q ∧
        ProhibitedSite N₀ ⌊L ^ (1/10 : ℝ)⌋₊ (fun d q => (d,q) ∈ data.pairs)
          ((b j+x.val : ℤ)+site j d q) then 1 else 0)
  have heach (j : ℤ) (hj : j ∈ bins) : cost j ≤ model j + data.pairs.card*Real.exp (-(L^9)) := by
    have he := hcmp N₀ J M B ⌊L ^ (1/10 : ℝ)⌋₊ (J+M) data hB hnonempty hBL hs hcap hpairs
      (fun dq hdq => prohibited_family_pair_degree data dq hdq) D hsupport hcard (padding j)
      (hret j hj) (hdegree j hj) (site j) (b j) (U j) (hU j hj)
    have hc : ((∑ d ∈ D, (padding j d).card : ℕ) : ℝ) ≤ data.pairs.card := by
      exact_mod_cast padding_pair_count_le D (padding j) data.pairs (hMembership j hj)
    have hdif := (le_abs_self _).trans he
    have hcerr := mul_le_mul_of_nonneg_right hc (Real.exp_pos (-(L^9))).le
    change cost j - model j ≤ _ at hdif
    linarith only [hdif,hcerr]
  have hmodels : (∑ j ∈ bins, model j) ≤ Real.exp (-L ^ (9/10 : ℝ)) := by
    by_cases he : bins = ∅
    · simp only [he,sum_empty]; positivity
    have hCount : (0 : ℝ) < bins.card := by exact_mod_cast card_pos.mpr (nonempty_iff_ne_empty.mpr he)
    have hpoint (j : ℤ) (hj : j ∈ bins) : (bins.card : ℝ)*model j ≤ Real.exp (-L ^ (9/10 : ℝ)) := by
      have he := hmodel N₀ hNlog hL η hB D (padding j) (fun _ _ => 0) bins.card hD (hret j hj)
        hCount.le hbins
      simpa only [add_zero,model,prohibitedPositiveRow,FiniteLaw.average_finset_sum,μ,data,B] using he
    have hh := sum_le_sum hpoint
    simp only [← mul_sum,sum_const,nsmul_eq_mul] at hh
    exact le_of_mul_le_mul_left hh hCount
  change (∑ j ∈ bins, cost j) ≤ _
  apply (sum_le_sum heach).trans
  simp only [sum_add_distrib,sum_const,nsmul_eq_mul]
  linarith only [hmodels]

#print axioms explicit_reflected_shifted_padding_deletion
#print axioms explicit_reflected_variable_rare_integer
end ReflectedLiouville
