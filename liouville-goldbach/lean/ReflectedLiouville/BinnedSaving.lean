import ReflectedLiouville.ActualKeptTotal
import ReflectedLiouville.ActualDeletionTotal
import ReflectedLiouville.ActualCenteringTotal

set_option autoImplicit false
set_option maxHeartbeats 1800000
open Filter
open scoped BigOperators Classical
open OAI.TwoPointCorrelations Finset
namespace ReflectedLiouville

lemma raw_kept_triangle (r c k : ℝ) : |r| ≤ |k| + |c-k| + |c-r| := by
  calc
    _ = |k+(c-k)+(r-c)| := by congr 1; ring
    _ ≤ |k+(c-k)| + |r-c| := abs_add_le _ _
    _ ≤ (|k|+|c-k|) + |c-r| := by
      rw [abs_sub_comm r c]
      exact add_le_add (abs_add_le _ _) le_rfl

theorem binned_reflected_saving (h_KMT : KMTInput) (h_MRT : MRTRealTwistRepulsionInput) :
    ∃ A : ℕ, 1000 ≤ A ∧ BinnedReflectedSaving A ((10 : ℝ)^(180 : ℕ)) (1/100000) := by
  let W := (10 : ℝ)^(180 : ℕ)
  have hW : 1 ≤ W := by dsimp only [W]; norm_num
  obtain ⟨Ak,hAk,hkept⟩ := actual_kept_total
  obtain ⟨Ad,hAd,hdeleted⟩ := actual_deletion_total bravermanDepth22Input
  let A := Ak+Ad
  have hA : 1000 ≤ A := by dsimp only [A]; omega
  have hApos : 0 < A := by omega
  have hAr : (0 : ℝ) < A := by exact_mod_cast hApos
  have hArone : (1 : ℝ) ≤ A := by exact_mod_cast (show 1 ≤ A by omega)
  obtain ⟨Cd,hCd,hdeleted⟩ := hdeleted (A : ℝ) hArone
  obtain ⟨Cc,Lc,hCc,hLc,Nc,hNc,hcentered⟩ := actual_centering_total h_KMT h_MRT A hA W hW
  let C := 2*(411+Cd+Cc)
  have hC : 0 < C := by dsimp only [C]; positivity
  let scale := fun N : ℕ => (Real.log (N : ℝ)) ^ (1/(A : ℝ))
  have hScale : Tendsto scale atTop atTop :=
    (tendsto_rpow_atTop (by positivity : 0 < 1/(A : ℝ))).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hevent : ∀ᶠ N : ℕ in atTop,
      |reflectedSum N|/(N : ℝ) ≤ C * Real.exp (-(reflectionBandCount W (1/100000) (scale N) : ℝ)) := by
    filter_upwards [hScale.eventually (hkept (A : ℝ)),hScale.eventually hdeleted,
      hScale.eventually (actual_raw_bins_dilation (A : ℝ) W (1/100000) hW (by norm_num) (by norm_num)),
      hScale.eventually (eventually_reflection_pool_range (A : ℝ) W (1/100000) hW (by norm_num) (by norm_num)),
      hScale.eventually (eventually_ge_atTop (max 1 Lc)),eventually_ge_atTop Nc,eventually_ge_atTop (3 : ℕ),
      tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (Real.exp 2))]
        with N hk hd hr hp hLlarge hNcenter hNthree hNexp
    letI : NeZero N := ⟨by omega⟩
    let L := scale N
    have hL : 1 ≤ L := (le_max_left _ _).trans hLlarge
    have hLp : 0 < L := by linarith
    have hLcenter : Lc ≤ L := (le_max_right _ _).trans hLlarge
    have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    have hLogId : Real.log (N : ℝ) = L ^ A := by
      symm
      dsimp only [L,scale]
      rw [← Real.rpow_natCast,← Real.rpow_mul hlog.le]
      have he : (1/(A : ℝ))*(A : ℝ) = 1 := by field_simp
      rw [he,Real.rpow_one]
    have hNlog : Real.log (N : ℝ) ≤ L ^ (A : ℝ) := by simpa only [Real.rpow_natCast] using hLogId.le
    have hLength (A' : ℕ) (hA' : A' ≤ A) : Real.exp (L ^ A' / 2) ≤ (N : ℝ) := by
      have hpow := pow_le_pow_right₀ hL hA'
      have hnonneg : 0 ≤ L ^ A' := pow_nonneg hLp.le _
      have he : L ^ A' / 2 ≤ L ^ A := by linarith only [hpow,hnonneg]
      apply (Real.exp_le_exp.mpr he).trans_eq
      rw [← hLogId,Real.exp_log hNr]
    let J := reflectionBandCount W (1/100000) L
    let η := Real.exp (-(J : ℝ))
    let data := reflectionPrimeFamily N W (1/100000) L η hL (by positivity : 0 ≤ W)
    let P := centeredPrimeBands N.primeFactors (L ^ (1-1/100000 : ℝ)) W J
    let S := paddingTiltNormalizer data.Q
    let V := ∏ k, primeHarmonicMass (P k)
    let M := S*V
    let S₀ := retainedPairMass data.pairs
    let bins := paddingBinIndices L η
    let raw := ∑ j ∈ bins, rawBinForm data.pairs N η j
    have hη : 0 < η := Real.exp_pos _
    have hrange := hp N hNlog hL η
    have hVone : 1 ≤ V := by
      apply one_le_prod₀
      intro k hk
      exact hW.trans (hrange.bandsLower k)
    have hS : 0 < S := paddingTiltNormalizer_pos _
    have hM : 0 < M := mul_pos hS (by linarith : 0 < V)
    have hkN := hk N hNlog (hLength Ak (by dsimp only [A]; omega)) hL
    have hdN := hd N hNexp hNlog (hLength Ad (by dsimp only [A]; omega)) hL
    have hcN := hcentered L hLcenter N hNcenter hLogId hL
    have hKept : (∑ j ∈ bins, |keptCenteredBinForm data L W η j|) ≤ 405*M*η := by
      convert hkN using 1 <;> dsimp only [M,S,V,P,data,η,J,bins,L] <;> ring
    have hDel : (∑ j ∈ bins, |centeredBinForm data.pairs N η j-keptCenteredBinForm data L W η j|) ≤ Cd*M*η := by
      convert hdN using 1 <;> dsimp only [M,S,V,P,data,η,J,bins,L] <;> ring
    have hCen : (∑ j ∈ bins, |centeredBinForm data.pairs N η j-rawBinForm data.pairs N η j|) ≤ Cc*M*η := by
      convert hcN using 1 <;> dsimp only [M,S,V,P,data,η,J,bins,L] <;> ring
    have hRaw : |raw| ≤ ((405+Cd+Cc)*η)*M := by
      apply (abs_sum_le_sum_abs _ _).trans
      apply (sum_le_sum (fun j _ => raw_kept_triangle (rawBinForm data.pairs N η j)
        (centeredBinForm data.pairs N η j) (keptCenteredBinForm data L W η j))).trans
      simp only [sum_add_distrib]
      have ht := add_le_add (add_le_add hKept hDel) hCen
      convert ht using 1 <;> ring
    have hJlog : (J : ℝ) ≤ Real.log L := by
      have hJ := hrange.countW
      have hj0 : (0 : ℝ) ≤ J := Nat.cast_nonneg _
      have hw := mul_le_mul_of_nonneg_left hW hj0
      change (J : ℝ)*(6*W) ≤ Real.log L at hJ
      nlinarith only [hJ,hw,hj0]
    have hEN : Real.exp (J : ℝ) ≤ (N : ℝ) := by
      have hEL : Real.exp (J : ℝ) ≤ L := by simpa only [Real.exp_log hLp] using Real.exp_le_exp.mpr hJlog
      have hLA : L ≤ L ^ A := by
        simpa only [pow_one] using pow_le_pow_right₀ hL (show 1 ≤ A by omega)
      have hLN : L ≤ Real.log (N : ℝ) := by simpa only [hLogId] using hLA
      have hlogN : Real.log (N : ℝ) ≤ (N : ℝ) := (Real.log_le_sub_one_of_pos hNr).trans (by linarith)
      exact hEL.trans (hLN.trans hlogN)
    have hRecip : 1/(N : ℝ) ≤ η := by
      dsimp only [η]
      rw [Real.exp_neg,inv_eq_one_div]
      exact div_le_div_of_nonneg_left zero_le_one (Real.exp_pos _) hEN
    obtain ⟨hDilation,hMass,_⟩ := hr N hNlog hL
    have hMass' : M/2 ≤ S₀ := by convert hMass using 1 <;> dsimp only [M,S,V,P,data,η,J,S₀,L] <;> ring
    have hDilation' : |raw-S₀*(reflectedSum N/(N : ℝ))| ≤ (6*η)*M := by
      have he : 4*η+2/(N : ℝ) ≤ 6*η := by
        have ht := mul_le_mul_of_nonneg_left hRecip (by norm_num : (0 : ℝ) ≤ 2)
        have ht' : 2/(N : ℝ) ≤ 2*η := by convert ht using 1 <;> ring
        calc
          _ ≤ 4*η+2*η := add_le_add le_rfl ht'
          _ = _ := by ring
      have hc := mul_le_mul_of_nonneg_right he hM.le
      apply hDilation.trans
      convert hc using 1 <;> dsimp only [M,S,V,P,data,η,J,raw,bins,S₀,L] <;> ring
    have hRecover := reflected_dilation_recovery raw (reflectedSum N/(N : ℝ)) S₀ M (6*η)
      ((405+Cd+Cc)*η) hM hMass' (by positivity) (by positivity) hRaw hDilation'
    rw [abs_div,abs_of_pos hNr] at hRecover
    convert hRecover using 1 <;> dsimp only [C,η,J,L] <;> ring
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp hevent
  refine ⟨A,hA,C,hC,max 3 N₀,le_max_left _ _,?_⟩
  intro N hN
  exact hN₀ N ((le_max_right _ _).trans hN)

#print axioms binned_reflected_saving
end ReflectedLiouville
