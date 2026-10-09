import ReflectedLiouville.DeletionScaleSaving
import ReflectedLiouville.ActualRawDilation

set_option autoImplicit false
set_option maxHeartbeats 1500000
open Filter
open scoped BigOperators Classical
open OAI.TwoPointCorrelations Finset
namespace ReflectedLiouville

theorem actual_deletion_total (hBr : BravermanDepth22Input) :
    ∃ Af : ℕ, 1000 ≤ Af ∧ ∀ (a₀ : ℝ), 1 ≤ a₀ →
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (N : ℕ) [NeZero N], Real.exp 2 ≤ (N : ℝ) → Real.log (N : ℝ) ≤ L ^ a₀ →
        Real.exp (L ^ Af / 2) ≤ (N : ℝ) → ∀ (hL : 1 ≤ L),
          let W := (10 : ℝ)^(180 : ℕ)
          let J := reflectionBandCount W (1/100000) L
          let η := Real.exp (-(J : ℝ))
          let data := reflectionPrimeFamily N W (1/100000) L η hL (by positivity)
          let P := centeredPrimeBands N.primeFactors (L ^ (1-1/100000 : ℝ)) W J
          (∑ j ∈ paddingBinIndices L η,
            |centeredBinForm data.pairs N η j - keptCenteredBinForm data L W η j|) ≤
            C * paddingTiltNormalizer data.Q * (∏ k, primeHarmonicMass (P k)) * η := by
  let W := (10 : ℝ)^(180 : ℕ)
  have hW : 10 ≤ W := by dsimp only [W]; norm_num
  have hWone : 1 ≤ W := by linarith
  obtain ⟨Af,hAf,hb⟩ := reflected_shifted_source_deletion hBr
  refine ⟨Af,hAf,?_⟩
  intro a₀ ha₀
  obtain ⟨C₁,hC₁,hb⟩ := hb a₀ ha₀ W (1/100000) 3 hW (by norm_num) (by norm_num) (by norm_num)
  refine ⟨2*(C₁+4),by positivity,?_⟩
  filter_upwards [hb,eventually_deletion_scale_saving W hWone,
    eventually_reflection_pool_range a₀ W (1/100000) hWone (by norm_num) (by norm_num),
    eventually_ge_atTop (101 : ℝ)] with L hsource hsmall hpool hLbig
  intro N inst hNexp hNlog hLength hLone
  dsimp only
  let J := reflectionBandCount W (1/100000) L
  let η := Real.exp (-(J : ℝ))
  let data := reflectionPrimeFamily N W (1/100000) L η hLone (by positivity : 0 ≤ W)
  let P := centeredPrimeBands N.primeFactors (L ^ (1-1/100000 : ℝ)) W J
  let D := primeTupleDivisors P
  let bins := paddingBinIndices L η
  let T := fun j => reflectionBinCutoff N η j
  let U := fun j => ⌊T j⌋₊
  let eligible := fun j => binPairEligible data.pairs η j
  let cost := fun site => reflectedShiftedSourceDeletion N W (1/100000) L η (Real.exp (4*J))
    hLone hWone bins (fun d => Real.log (d : ℝ)) eligible site (fun _ => 1) U
  let S := paddingTiltNormalizer data.Q
  let V := ∏ k, primeHarmonicMass (P k)
  have hrange := hpool N hNlog hLone η
  have hS : 0 < S := paddingTiltNormalizer_pos _
  have hVone : 1 ≤ V := by
    apply one_le_prod₀
    intro k hk
    exact hWone.trans (hrange.bandsLower k)
  have hV : 0 < V := by linarith
  have hSV : 0 < S*V := mul_pos hS hV
  have hη : 0 < η := Real.exp_pos _
  have hηhalf : η ≤ 1/2 := exp_negative_count_le_half J hrange.oneJ
  have hηone : η ≤ 1 := by linarith
  have hbins : (bins.card : ℝ) ≤ Real.exp (3*Real.log L) :=
    reflection_bin_card_polynomial W (1/100000) L hWone (by norm_num) (by norm_num) hLbig
  have hsub := reflection_pair_supply_subset N W (1/100000) L η hLone (by positivity : 0 ≤ W)
  have hWindow (j : ℤ) (hj : j ∈ bins) : (N : ℝ) ≤ T j :=
    (reflected_bin_frame_geometry N (NeZero.pos N) L η (by linarith) hη hηhalf j hj).1
  have hU (j : ℤ) (hj : j ∈ bins) : Real.exp (L ^ Af / 2) ≤ (U j : ℝ) := by
    have hn : N ≤ U j := Nat.le_floor (hWindow j hj)
    exact hLength.trans (by exact_mod_cast hn)
  have hBpos (j : ℤ) (hj : j ∈ bins) : 0 < U j := by
    have hn : N ≤ U j := Nat.le_floor (hWindow j hj)
    have hh := NeZero.pos N
    omega
  have hbin (j : ℤ) (hj : j ∈ bins) (d q : ℕ) (he : eligible j d q) :
      actualPaddingBin η (Real.log (d : ℝ)) j q :=
    reflected_eligible_actual_bin data.pairs d q
      (Nat.pos_of_ne_zero (data.tuple_squarefree _ he.1).ne_zero)
      (Nat.pos_of_ne_zero (data.padding_squarefree _ he.1).ne_zero) η hη j he
  have hcost (site : ℤ → ℕ → ℕ → ℤ) : cost site / (S*V) ≤ (C₁+4)*η := by
    have he := hsource N hNexp hNlog hLone η (Real.exp (4*J)) hη hηone (Real.exp_pos _)
      bins (fun d => Real.log (d : ℝ)) eligible hbins (fun _ _ _ _ he => he.1) hbin
      site (fun _ => 1) U hU
    exact he.trans (hsmall C₁ hC₁.le)
  have hLoss : (∑ j ∈ bins,
      |centeredBinForm data.pairs N η j - keptCenteredBinForm data L W η j|) ≤
      cost (fun _ _ _ => 0) + cost (fun _ d q => -((N*d*q : ℕ) : ℤ)) := by
    have hb (j : ℤ) (hj : j ∈ bins) := reflected_deletion_bin_bound data D hsub L W η hη j
      ((by exact_mod_cast NeZero.pos N : (0 : ℝ) < N).trans_le (hWindow j hj)) (hBpos j hj)
    apply (sum_le_sum hb).trans_eq
    simp only [sum_add_distrib]
    congr 1
    all_goals dsimp only [cost,reflectedShiftedSourceDeletion]
    all_goals apply sum_congr rfl
    all_goals intro j hj
    all_goals apply sum_congr rfl
    all_goals intro d hd
    all_goals apply sum_congr rfl
    all_goals intro q hq
    all_goals apply congrArg uniformAverage
    all_goals funext x
    all_goals congr 1
    all_goals push_cast
    all_goals ring
  have hBoth := add_le_add (hcost (fun _ _ _ => 0)) (hcost (fun _ d q => -((N*d*q : ℕ) : ℤ)))
  have he : (∑ j ∈ bins,
      |centeredBinForm data.pairs N η j - keptCenteredBinForm data L W η j|) / (S*V) ≤ 2*(C₁+4)*η := by
    apply (div_le_div_of_nonneg_right hLoss hSV.le).trans
    rw [add_div]
    convert hBoth using 1 <;> ring
  have hs := (div_le_iff₀ hSV).mp he
  convert hs using 1 <;> dsimp only [S,V,P,data,η,J,bins] <;> ring

#print axioms actual_deletion_total
end ReflectedLiouville
