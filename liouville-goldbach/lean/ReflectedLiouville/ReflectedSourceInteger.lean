import ReflectedLiouville.ReflectedPaddingInteger
import ReflectedLiouville.ReflectedRareInteger
import OAI.NumberTheory.TwoPoint.Bounds.ShiftedDegreeDeletion
import OAI.NumberTheory.TwoPoint.Bounds.DeletionNormalization
import OAI.NumberTheory.TwoPoint.Bounds.DeletionErrorScale
import OAI.NumberTheory.TwoPoint.Bounds.PrimeAlphabetSize

set_option autoImplicit false
set_option maxHeartbeats 1500000
open Finset Filter
open scoped BigOperators Classical
open OAI.TwoPointCorrelations
namespace ReflectedLiouville

noncomputable def reflectedShiftedSourceDeletion (N₀ : ℕ) [NeZero N₀] (W δ L η K : ℝ)
    (hL : 1 ≤ L) (hW : 1 ≤ W)
    (bins : Finset ℤ) (c : ℕ → ℝ) (eligible : ℤ → ℕ → ℕ → Prop)
    (site : ℤ → ℕ → ℕ → ℤ) (a N : ℤ → ℕ) : ℝ :=
  let J := reflectionBandCount W δ L
  let P := centeredPrimeBands N₀.primeFactors (L ^ (1-δ)) W J
  let Q := paddingPrimeSupply N₀.primeFactors L
  let R := boundedPaddingDivisors Q ⌊100 * Real.log L⌋₊
  let bad := fun (_ : ℤ) n => ProhibitedSite N₀ ⌊L ^ (1/10 : ℝ)⌋₊
    (fun d q => (d,q) ∈ (reflectionPrimeFamily N₀ W δ L η hL (by linarith)).pairs) n
  ∑ j ∈ bins, ∑ d ∈ primeTupleDivisors P, ∑ q ∈ R,
    uniformAverage (fun x : Fin (N j) => positiveDeletionAtom (primeTuplePool P) Q R
      η c L K W eligible bad j d q ((a j + x.val : ℤ) + site j d q))

theorem reflected_shifted_source_deletion (hBr : BravermanDepth22Input) :
    ∃ Af : ℕ, 1000 ≤ Af ∧ ∀ (a₀ : ℝ) (ha₀ : 1 ≤ a₀)
      (W δ Cbins : ℝ) (hW : 10 ≤ W) (hδ : 0 < δ) (hδsmall : δ ≤ 1/200) (hC : 0 ≤ Cbins),
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (N₀ : ℕ) [NeZero N₀], Real.exp 2 ≤ (N₀ : ℝ) → Real.log (N₀ : ℝ) ≤ L ^ a₀ →
      ∀ (hL : 1 ≤ L) (η K : ℝ), 0 < η → η ≤ 1 → 0 < K →
      ∀ (bins : Finset ℤ) (c : ℕ → ℝ) (eligible : ℤ → ℕ → ℕ → Prop),
      (bins.card : ℝ) ≤ Real.exp (Cbins*Real.log L) →
      (∀ j ∈ bins, ∀ d q, eligible j d q →
        (d,q) ∈ (reflectionPrimeFamily N₀ W δ L η hL (by linarith)).pairs) →
      (∀ j ∈ bins, ∀ d q, eligible j d q → actualPaddingBin η (c d) j q) →
      ∀ (site : ℤ → ℕ → ℕ → ℤ) (a N : ℤ → ℕ),
      (∀ j ∈ bins, Real.exp (L ^ Af / 2) ≤ (N j : ℝ)) →
      let J := reflectionBandCount W δ L
      let P := centeredPrimeBands N₀.primeFactors (L ^ (1-δ)) W J
      reflectedShiftedSourceDeletion N₀ W δ L η K hL (by linarith) bins c eligible site a N /
        (paddingTiltNormalizer (paddingPrimeSupply N₀.primeFactors L)*∏ j, primeHarmonicMass (P j)) ≤
        (2 : ℝ)^J*(C*(Real.log L)^(10 : ℕ)/K + L ^ (-90 : ℝ) + Real.exp (-2*W*J)) +
          2*Real.exp (-L ^ (9/10 : ℝ)) := by
  obtain ⟨Ap, hAp, hp⟩ := reflected_shifted_padding_deletion hBr
  obtain ⟨Ad, hAd, hd⟩ := hBr.eventually_shifted_tuple_degree_deletion
  obtain ⟨Ar, hAr, hr⟩ := reflected_variable_rare_integer hBr
  let A := Ap + Ad + Ar
  refine ⟨A, by dsimp [A]; omega, ?_⟩
  intro a₀ ha₀ W δ Cbins hW hδ hδsmall hC
  obtain ⟨Cp,hCp,hp⟩ := hp a₀ ha₀
  have hr := hr a₀ W δ Cbins hW hδ hδsmall hC
  refine ⟨Cp, hCp, ?_⟩
  filter_upwards [hp, hd, hr, eventually_reflection_pool_range a₀ W δ (by linarith) hδ (by linarith),
    eventually_deletion_comparison_error Cbins hC, eventually_ge_atTop (4800 : ℝ)]
      with L hp hd hr hm herr hlarge
  intro N₀ inst hN₀ hN₀log hL η K hη hηone hK bins c eligible hbins helig hbin site a N hN
  dsimp only
  let J := reflectionBandCount W δ L
  let P := centeredPrimeBands N₀.primeFactors (L ^ (1-δ)) W J
  let Q := paddingPrimeSupply N₀.primeFactors L
  let R := boundedPaddingDivisors Q ⌊100 * Real.log L⌋₊
  let D := primeTupleDivisors P
  let data := reflectionPrimeFamily N₀ W δ L η hL (by linarith : 0 ≤ W)
  have hm := hm N₀ hN₀log hL η
  let hB := hm.residueBound
  let bad := fun (_ : ℤ) n => ProhibitedSite N₀ ⌊L ^ (1/10 : ℝ)⌋₊
    (fun d q => (d,q) ∈ data.pairs) n
  let S := paddingTiltNormalizer Q
  let V := ∏ j, primeHarmonicMass (P j)
  let pad := ∑ j ∈ bins, ∑ d ∈ D, ∑ q ∈ R, uniformAverage (fun x : Fin (N j) =>
    paddingRejectionAtom Q d.primeFactors R (actualPaddingBin η (c d) j) L K q
      ((a j + x.val : ℤ) + site j d q))
  let deg := ∑ j ∈ bins, ∑ d ∈ D, ∑ q ∈ R.filter (actualPaddingBin η (c d) j),
    uniformAverage (fun x : Fin (N j) =>
      positiveDegreeCost (primeTuplePool P) d.primeFactors W q ((a j + x.val : ℤ) + site j d q))
  let rare := ∑ j ∈ bins, ∑ d ∈ D, ∑ q ∈ R.filter (eligible j d),
    uniformAverage (fun x : Fin (N j) => actualPaddingCoefficient q *
      positivePrimeWeight d.primeFactors ((a j + x.val : ℤ) + site j d q) *
        if (q : ℤ) ∣ ((a j + x.val : ℤ) + site j d q) ∧ bad j ((a j + x.val : ℤ) + site j d q)
          then 1 else 0)
  have hN' (A' : ℕ) (hA' : A' ≤ A) (j : ℤ) (hj : j ∈ bins) :
      Real.exp (L ^ A' / 2) ≤ (N j : ℝ) :=
    (Real.exp_le_exp.mpr (div_le_div_of_nonneg_right
      (pow_le_pow_right₀ hL hA') (by norm_num))).trans (hN j hj)
  have hprime : ∀ j, ∀ p ∈ P j, p.Prime := centeredPrimeBands_prime _ _ _ _
  have hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l) :=
    centeredPrimeBands_disjoint _ _ _ _ (Real.rpow_nonneg (zero_le_one.trans hL) _) (by linarith)
  have hpool : (data.P ∪ data.Q).Nonempty := by
    by_contra hn
    have hempty : data.P = ∅ := not_nonempty_iff_eq_empty.mp
      (fun hp => hn (hp.mono subset_union_left))
    have hx := hm.centerLower
    change 1 ≤ primeHarmonicMass data.P at hx
    rw [hempty] at hx
    norm_num [primeHarmonicMass] at hx
  have hJ : (J : ℝ) ≤ L^2 := by
    have ht := hm.slots
    have hj : (J : ℝ) ≤ ((J+⌊100*Real.log L⌋₊ : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right J _
    have hl : Real.log L ≤ L := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
    exact hj.trans (ht.trans (by nlinarith))
  have hR : R ⊆ retainedPrimeDivisors data.Q := filter_subset _ _
  have hdegree : ∀ q ∈ R, (q.primeFactors.card : ℝ) ≤ 100 * Real.log L := by
    intro q hq
    have hx : (q.primeFactors.card : ℝ) ≤ (⌊100 * Real.log L⌋₊ : ℝ) := by
      exact_mod_cast (mem_filter.mp hq).2
    exact hx.trans hm.paddingDegree
  have hpad := hp N₀ hN₀ hN₀log N₀ J ⌊100 * Real.log L⌋₊ ⌊Real.exp L⌋₊ data rfl hB hpool
    (Nat.floor_le (Real.exp_pos _).le) P rfl hprime hdisjoint hJ D subset_rfl R hR hdegree
      bins η K c hη hηone hK site a N (hN' Ap (by dsimp [A]; omega))
  have hdeg := hd N₀ J ⌊100 * Real.log L⌋₊ ⌊Real.exp L⌋₊ data hB hpool
    (Nat.floor_le (Real.exp_pos _).le) P rfl hprime hdisjoint W hW
      hm.bandsUpper hJ
      (by have ht := hm.countW; nlinarith [Real.log_nonneg hL])
      D subset_rfl R hR hdegree bins η c hη site a N (hN' Ad (by dsimp [A]; omega))
  have hrare := hr N₀ hN₀log hL η hη hηone D
    (fun j d => R.filter (eligible j d)) bins subset_rfl
    (fun j hj d hd => filter_subset _ _)
    (fun j hj d hd q hq => helig j hj d q (mem_filter.mp hq).2)
    hbins site a N (hN' Ar (by dsimp [A]; omega))
  have hpair := (reflection_family_support N₀ W δ L η hL (by linarith) hδ.le hη hηone).2
  have hrare' : rare ≤ Real.exp (-L ^ (9/10 : ℝ)) +
      bins.card*Real.exp (101*L)*Real.exp (-(L^9)) := by
    change rare ≤ Real.exp (-L ^ (9/10 : ℝ)) + bins.card*data.pairs.card*Real.exp (-(L^9)) at hrare
    apply hrare.trans
    have hc := mul_le_mul_of_nonneg_left hpair (Nat.cast_nonneg bins.card : (0 : ℝ) ≤ bins.card)
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hc (Real.exp_pos (-(L^9))).le)
  have hS : 1 ≤ S := paddingTiltNormalizer_one_le Q
  have hV : 1 ≤ V := by
    apply one_le_prod₀
    intro j _
    exact (by linarith : 1 ≤ W).trans (hm.bandsLower j)
  have hDcard : (D.card : ℝ) ≤ Real.exp (2 * L) := by
    have hc : D.card ≤ Fintype.card ((j : Fin J) → P j) := by
      exact (card_image_le).trans_eq card_univ
    have ht := primeTuple_card_le P hprime hdisjoint ⌊Real.exp (2 * L)⌋₊ (fun d =>
      centeredPrimeTuple_upper N₀.primeFactors _ W L J
        (Real.rpow_pos_of_pos (zero_lt_one.trans_le hL) _) (by linarith)
        (reflection_prime_endpoint W δ L (by linarith) hδ.le hL) (mem_image.mpr ⟨d, mem_univ _, rfl⟩))
    exact (show (D.card : ℝ) ≤ (⌊Real.exp (2 * L)⌋₊ : ℝ) by exact_mod_cast hc.trans ht).trans
      (Nat.floor_le (Real.exp_pos _).le)
  have herror := herr bins.card D.card R.card S V (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) hbins hDcard (boundedPaddingDivisors_card N₀.primeFactors L hL) hS hV
  have hsplit := shifted_source_deletion_split (primeTuplePool P) Q D R bins η c L K W
    eligible bad (fun j hj d _ q _ => hbin j hj d q) site a N
  have hpad' : pad ≤ S * V * (2 : ℝ) ^ J * (Cp*(Real.log L)^(10 : ℕ)/K + L ^ (-90 : ℝ)) +
      2 * bins.card * D.card * R.card * Real.exp (-(L ^ 9)) := by
    change pad / S ≤ (2 : ℝ) ^ J * V * (Cp*(Real.log L)^(10 : ℕ)/K + L ^ (-90 : ℝ)) +
      (2 * bins.card * D.card * R.card * Real.exp (-(L ^ 9))) / S at hpad
    have hx := (div_le_iff₀ (show 0 < S from paddingTiltNormalizer_pos Q)).mp hpad
    rw [add_mul, div_mul_cancel₀ _ (show 0 < S from paddingTiltNormalizer_pos Q).ne'] at hx
    nlinarith
  have hdeg' : deg ≤ S * V * (2 : ℝ) ^ J * Real.exp (-2 * W * J) +
      bins.card * D.card * R.card * Real.exp (-(L ^ 9)) := by
    change deg ≤ ((2 : ℝ) ^ J * V) * S * Real.exp (-2 * W * J) +
      bins.card * D.card * R.card * Real.exp (-(L ^ 9)) at hdeg
    convert hdeg using 1; ring
  have hn := normalize_three_deletion_costs
    (reflectedShiftedSourceDeletion N₀ W δ L η K hL (by linarith) bins c eligible site a N)
    pad deg rare S V ((2 : ℝ) ^ J) (Cp*(Real.log L)^(10 : ℕ)/K + L ^ (-90 : ℝ))
      (Real.exp (-2 * W * J)) (Real.exp (-L ^ (9 / 10 : ℝ)))
      (2 * bins.card * D.card * R.card * Real.exp (-(L ^ 9)))
      (bins.card * D.card * R.card * Real.exp (-(L ^ 9)))
      (bins.card * Real.exp (101 * L) * Real.exp (-(L ^ 9)))
    hS hV (Real.exp_pos _).le hsplit hpad' hdeg' hrare'
  have heq :
      (2 * bins.card * D.card * R.card * Real.exp (-(L ^ 9)) +
        bins.card * D.card * R.card * Real.exp (-(L ^ 9)) +
        bins.card * Real.exp (101 * L) * Real.exp (-(L ^ 9))) /
        (S * V) ≤ Real.exp (-L ^ (9 / 10 : ℝ)) := by
    convert herror using 1; ring
  change _ / (S * V) ≤ _
  linarith

#print axioms reflected_shifted_source_deletion
end ReflectedLiouville
