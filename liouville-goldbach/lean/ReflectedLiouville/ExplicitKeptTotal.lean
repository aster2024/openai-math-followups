import ReflectedLiouville.ExplicitAffineGraph
import ReflectedLiouville.ExplicitTestEnergy
import ReflectedLiouville.ActualKeptTotal

set_option autoImplicit false
set_option maxHeartbeats 1800000
open OAI.TwoPointCorrelations Finset Filter
open scoped BigOperators Classical
namespace ReflectedLiouville

theorem explicit_kept_operator_bilinear_bound (W δ : ℝ) (hW : 1 ≤ W)
    (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 200) :
    ∀ a : ℝ, ∀ᶠ L : ℝ in atTop,
      ∀ (N : ℕ) [NeZero N], Real.log (N : ℝ) ≤ L ^ a → Real.exp (L ^ (289578 : ℕ) / 2) ≤ (N : ℝ) →
        ∀ (hL : 1 ≤ L) (T U : ℝ), (N : ℝ) ≤ T → (N : ℝ) ≤ U → U ≤ 3 * T →
          let J := reflectionBandCount W δ L
          let η := Real.exp (-(J : ℝ))
          let data := reflectionPrimeFamily N W δ L η hL (by linarith)
          let P := centeredPrimeBands N.primeFactors (L ^ (1 - δ)) W J
          let MB := ⌈Real.exp (103 * L)⌉₊
          let site := fun i : Fin MB => (i.val : ℤ) - (MB / 2 : ℕ)
          let B := Real.exp (4 * J) * (((3 : ℝ) ^ (170 : ℕ)) * Real.sqrt W) ^ J
          ∀ j : ℤ,
            (∑ r : Fin N, ‖inner ℂ
              (sourceTestVector data.Q T L (fun i => (N : ℤ) * site i + ((r.val + 1 : ℕ) : ℤ)))
              (physicalReflectionCompression data P site ((r.val + 1 : ℕ) : ℤ) L W (binPairEligible data.pairs η j)
                (targetTestVector data.Q U L (fun i => (N : ℤ) * site i + ((r.val + 1 : ℕ) : ℤ))))‖) ≤
              4 * paddingTiltNormalizer data.Q * T * B +
                (T / N + 1) * (2 * Real.exp (4 * J) * (8 * W) ^ J) * (5 : ℝ) ^ (400 * Real.log L) *
                  Real.exp (-(2 * ⌊L⌋₊ : ℕ)) * N := by
  let Ac := 144789
  let Av := 144789
  have hcomp := explicit_reflected_compression_bound W δ hW hδ hδsmall
  have henergy := explicit_reflected_test_energy_bound
  intro a
  filter_upwards [hcomp a, henergy, eventually_reflection_pool_range a W δ hW hδ (by linarith)]
    with L hcompress hnorm hpool
  intro N inst hNlog hlength hL T U hNT hNU hUT
  dsimp only
  let J := reflectionBandCount W δ L
  let η := Real.exp (-(J : ℝ))
  let data := reflectionPrimeFamily N W δ L η hL (by linarith : 0 ≤ W)
  let P := centeredPrimeBands N.primeFactors (L ^ (1 - δ)) W J
  let MB := ⌈Real.exp (103 * L)⌉₊
  let site := fun i : Fin MB => (i.val : ℤ) - (MB / 2 : ℕ)
  let B := Real.exp (4 * J) * (((3 : ℝ) ^ (170 : ℕ)) * Real.sqrt W) ^ J
  let D := (T / N + 1) * (2 * Real.exp (4 * J) * (8 * W) ^ J) * (5 : ℝ) ^ (400 * Real.log L)
  have hn : 0 < N := NeZero.pos N
  have hNr : (0 : ℝ) < N := by exact_mod_cast hn
  have hT : 0 < T := hNr.trans_le hNT
  have hNc : Real.exp (L ^ Ac / 2) ≤ (N : ℝ) :=
    (Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (pow_le_pow_right₀ hL ((by norm_num : (144789 : ℕ) ≤ 289578))) (by norm_num))).trans hlength
  have hNv : Real.exp (L ^ Av / 2) ≤ (N : ℝ) :=
    (Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (pow_le_pow_right₀ hL ((by norm_num : (144789 : ℕ) ≤ 289578))) (by norm_num))).trans hlength
  have hrange := hpool N hNlog hL η
  obtain ⟨ell, hlarge, hinv, htail⟩ := hcompress N hNlog hNc hL
  have hsite : Function.Injective site := by
    intro i j he
    apply Fin.ext
    dsimp only [site] at he
    omega
  have hQupper : ∀ p ∈ data.Q, (p : ℝ) ≤ Real.exp L := by
    intro p hp
    have hpb : p ≤ ⌊Real.exp L⌋₊ := hrange.residueBound p (Finset.mem_union_right _ hp)
    exact (show (p : ℝ) ≤ (⌊Real.exp L⌋₊ : ℝ) by exact_mod_cast hpb).trans (Nat.floor_le (Real.exp_pos _).le)
  have hE := hnorm data.Q data.primeQ hQupper N T U hn hNT hNU hUT hNv (Fin MB) site hsite
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  intro j
  let A := fun r : Fin N => physicalReflectionCompression data P site ((r.val + 1 : ℕ) : ℤ) L W
    (binPairEligible data.pairs η j)
  let f := fun r : Fin N => sourceTestVector data.Q T L (fun i => (N : ℤ) * site i + ((r.val + 1 : ℕ) : ℤ))
  let g := fun r : Fin N => targetTestVector data.Q U L (fun i => (N : ℤ) * site i + ((r.val + 1 : ℕ) : ℤ))
  have hEllOff : MB / 2 ≤ ell := by have := Nat.div_le_self MB 2; omega
  have hOp (r : Fin N) : A r =
      reflectionCompressedGraph (quotientPrimeFamily data) P L W (binPairEligible data.pairs η j) (fun _ _ _ => True)
        (((ell - MB / 2 + ell * r.val : ℕ) : ℤ)) := by
    have ho := physical_compression_eq_block data hrange.residueBound hn P hrange.bandPrimes
      hrange.bandDisjoint hrange.bandSubset
      (fun d q hdq => reflection_pair_coprime_total N W δ L η hL (by linarith) d q hdq)
      ell (MB / 2) hinv ((r.val + 1 : ℕ) : ℤ) L W (binPairEligible data.pairs η j)
    have hc : ((ell - MB / 2 + ell * r.val : ℕ) : ℤ) =
        (ell : ℤ) * ((r.val + 1 : ℕ) : ℤ) - (MB / 2 : ℕ) := by
      rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hEllOff]
      push_cast
      ring
    rw [← hc] at ho
    exact ho
  have hbadMean : uniformAverage (fun r : Fin N => if B < ‖A r‖ then (1 : ℝ) else 0) ≤
      Real.exp (-(2 * ⌊L⌋₊ : ℕ)) := by
    have ht := htail j
    change uniformAverage (fun r : Fin N => if B < ‖A r‖ then (1 : ℝ) else 0) ≤ _
    simp only [hOp]
    convert ht using 1
    congr 1
  have hcount : (∑ r : Fin N, if B < ‖A r‖ then (1 : ℝ) else 0) ≤
      Real.exp (-(2 * ⌊L⌋₊ : ℕ)) * N := by
    simp only [uniformAverage, Fintype.card_fin] at hbadMean
    exact (div_le_iff₀ hNr).mp hbadMean
  have hbad : ∀ r : Fin N, B < ‖A r‖ → ‖inner ℂ (f r) (A r (g r))‖ ≤ D := by
    intro r hbad
    have hr : 1 ≤ ((r.val + 1 : ℕ) : ℤ) ∧ ((r.val + 1 : ℕ) : ℤ) ≤ (N : ℤ) := by
      exact_mod_cast (show 1 ≤ r.val + 1 ∧ r.val + 1 ≤ N by have := r.isLt; omega)
    exact physical_reflected_sparse_bound data P hrange.bandPrimes hrange.bandDisjoint site hsite hn _ hr
      L W T U (by linarith) (by linarith) hT.le hrange.bandsUpper (binPairEligible data.pairs η j)
  have hb := finite_good_bad_bilinear A f g B D (8 * paddingTiltNormalizer data.Q * T)
    (Real.exp (-(2 * ⌊L⌋₊ : ℕ))) hB hD hE (by simpa only [Fintype.card_fin] using hcount) hbad
  change (∑ r : Fin N, ‖inner ℂ (f r) (A r (g r))‖) ≤
    4 * paddingTiltNormalizer data.Q * T * B + D * Real.exp (-(2 * ⌊L⌋₊ : ℕ)) * N
  simp only [Fintype.card_fin] at hb
  convert hb using 1 <;> ring

theorem explicit_actual_kept_bin_bound (W δ : ℝ) (hW : 1 ≤ W) (hδ : 0 < δ) (hδsmall : δ ≤ 1/200) :
    ∀ a : ℝ, ∀ᶠ L : ℝ in atTop,
      ∀ (N : ℕ) [NeZero N], Real.log (N : ℝ) ≤ L ^ a → Real.exp (L ^ (289578 : ℕ) / 2) ≤ (N : ℝ) →
        ∀ (hL : 1 ≤ L),
          let J := reflectionBandCount W δ L
          let η := Real.exp (-(J : ℝ))
          let data := reflectionPrimeFamily N W δ L η hL (by linarith)
          ∀ j ∈ paddingBinIndices L η,
            |keptCenteredBinForm data L W η j| ≤
              4 * paddingTiltNormalizer data.Q / L *
                (Real.exp (4*J) * (((3 : ℝ)^(170 : ℕ))*Real.sqrt W)^J) +
              4 * Real.exp (4*J) * (8*W)^J * (5 : ℝ)^(400*Real.log L) *
                Real.exp (-(2*⌊L⌋₊ : ℕ)) / L := by
  have hb := explicit_kept_operator_bilinear_bound W δ hW hδ hδsmall
  intro a
  filter_upwards [hb a,eventually_reflectionBandCount_positive W δ (by linarith) hδ,
    eventually_ge_atTop (2 : ℝ)] with L hoperator hJ hLtwo
  intro N inst hNlog hLength hLone
  dsimp only
  let J := reflectionBandCount W δ L
  let η := Real.exp (-(J : ℝ))
  let data := reflectionPrimeFamily N W δ L η hLone (by linarith : 0 ≤ W)
  let P := centeredPrimeBands N.primeFactors (L ^ (1-δ)) W J
  let MB := ⌈Real.exp (103*L)⌉₊
  let site := fun i : Fin MB => (i.val : ℤ) - (MB/2 : ℕ)
  let B := Real.exp (4*J) * (((3 : ℝ)^(170 : ℕ))*Real.sqrt W)^J
  let E := Real.exp (4*J) * (8*W)^J * (5 : ℝ)^(400*Real.log L) * Real.exp (-(2*⌊L⌋₊ : ℕ))
  have hn := NeZero.pos N
  have hNr : (0 : ℝ) < N := by exact_mod_cast hn
  have hLp : 0 < L := by linarith
  have hη : 0 < η := Real.exp_pos _
  have hηsmall : η ≤ 1/2 := by
    have hJr : (1 : ℝ) ≤ J := by exact_mod_cast hJ
    have hExp : (2 : ℝ) ≤ Real.exp (J : ℝ) := Real.exp_one_gt_two.le.trans (Real.exp_le_exp.mpr hJr)
    dsimp only [η]
    rw [Real.exp_neg]
    have hi := (inv_le_inv₀ (Real.exp_pos (J : ℝ)) (by norm_num : (0 : ℝ) < 2)).mpr hExp
    simpa only [one_div] using hi
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  intro j hj
  let T := reflectionBinCutoff N η j
  let U := Real.exp η * T
  have hf := reflected_bin_frame_geometry N hn L η hLtwo hη hηsmall j hj
  dsimp only at hf
  have hT : 0 < T := hNr.trans_le hf.1
  have hform := actual_kept_pairing N W δ L η hLtwo (by linarith) hη hηsmall j hj
  have hbound := hoperator N hNlog hLength hLone T U hf.1 hf.2.1 hf.2.2.1 j
  let pairing := fun r : Fin N => inner ℂ
    (sourceTestVector data.Q T L (fun i => (N : ℤ)*site i + ((r.val+1 : ℕ) : ℤ)))
    (physicalReflectionCompression data P site ((r.val+1 : ℕ) : ℤ) L W
      (binPairEligible data.pairs η j)
      (targetTestVector data.Q U L (fun i => (N : ℤ)*site i + ((r.val+1 : ℕ) : ℤ))))
  have hPair : (∑ r : Fin N, pairing r) = ((L*T*keptCenteredBinForm data L W η j : ℝ) : ℂ) := hform
  have hNorm : L*T*|keptCenteredBinForm data L W η j| ≤
      4*paddingTiltNormalizer data.Q*T*B + (T/N+1)*2*E*N := by
    have he := (norm_sum_le Finset.univ pairing).trans hbound
    rw [hPair, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_pos hLp, abs_of_pos hT] at he
    convert he using 1 <;> dsimp only [E] <;> ring
  have hError : (T/N+1)*2*E*N ≤ 4*E*T := by
    have he : (T/N+1)*2*E*N = 2*E*(T+N) := by field_simp <;> ring
    rw [he]
    have hNT : (N : ℝ) ≤ T := hf.1
    nlinarith only [hNT,hE]
  have hs : L*T*|keptCenteredBinForm data L W η j| ≤ 4*paddingTiltNormalizer data.Q*T*B + 4*E*T := by
    linarith only [hNorm,hError]
  have hResult : |keptCenteredBinForm data L W η j| ≤ 4*paddingTiltNormalizer data.Q/L*B + 4*E/L := by
    calc
      _ ≤ (4*paddingTiltNormalizer data.Q*T*B + 4*E*T)/(L*T) :=
        (le_div_iff₀ (mul_pos hLp hT)).mpr (by nlinarith only [hs])
      _ = _ := by field_simp <;> ring
  convert hResult using 1 <;> dsimp only [E,B,data,η,J] <;> ring

theorem explicit_actual_kept_total :
    ∀ a : ℝ, ∀ᶠ L : ℝ in atTop,
      ∀ (N : ℕ) [NeZero N], Real.log (N : ℝ) ≤ L ^ a → Real.exp (L ^ (289578 : ℕ) / 2) ≤ (N : ℝ) →
        ∀ (hL : 1 ≤ L),
          let W := (10 : ℝ)^(180 : ℕ)
          let J := reflectionBandCount W (1/100000) L
          let η := Real.exp (-(J : ℝ))
          let data := reflectionPrimeFamily N W (1/100000) L η hL (by positivity)
          let P := centeredPrimeBands N.primeFactors (L ^ (1-1/100000 : ℝ)) W J
          (∑ j ∈ paddingBinIndices L η, |keptCenteredBinForm data L W η j|) ≤
            405 * paddingTiltNormalizer data.Q * (∏ k, primeHarmonicMass (P k)) * η := by
  let W := (10 : ℝ)^(180 : ℕ)
  have hW : 1 ≤ W := by dsimp only [W]; norm_num
  have hb := explicit_actual_kept_bin_bound W (1/100000) hW (by norm_num) (by norm_num)
  intro a
  filter_upwards [hb a,eventually_reflection_pool_range a W (1/100000) hW (by norm_num) (by norm_num),
    eventually_kept_bad_decay W (1/100000) hW (by norm_num) (by norm_num),
    eventually_ge_atTop (2 : ℝ)] with L hbound hpool hbad hLtwo
  intro N inst hNlog hLength hLone
  dsimp only
  let J := reflectionBandCount W (1/100000) L
  let η := Real.exp (-(J : ℝ))
  let data := reflectionPrimeFamily N W (1/100000) L η hLone (by positivity : 0 ≤ W)
  let P := centeredPrimeBands N.primeFactors (L ^ (1-1/100000 : ℝ)) W J
  let S := paddingTiltNormalizer data.Q
  let V := ∏ k, primeHarmonicMass (P k)
  let B := Real.exp (4*J) * (((3 : ℝ)^(170 : ℕ))*Real.sqrt W)^J
  let E := Real.exp (4*J) * (8*W)^J * (5 : ℝ)^(400*Real.log L) * Real.exp (-(2*⌊L⌋₊ : ℕ))
  have hrange := hpool N hNlog hLone η
  have hVone : 1 ≤ V := by
    calc
      _ = ∏ _k : Fin J, (1 : ℝ) := by simp
      _ ≤ _ := prod_le_prod₀ (fun _ _ => zero_le_one) (fun k _ => hW.trans (hrange.bandsLower k))
  have hWV : W^J ≤ V := by
    calc
      _ = ∏ _k : Fin J, W := by simp
      _ ≤ _ := prod_le_prod₀ (fun _ _ => by linarith) (fun k _ => hrange.bandsLower k)
  have hSone : 1 ≤ S := paddingTiltNormalizer_one_le _
  have hS : 0 < S := paddingTiltNormalizer_pos _
  have hV : 0 < V := by linarith
  have hη : 0 < η := Real.exp_pos _
  have hηone : η ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Nat.cast_nonneg _))
  have hLpos : 0 < L := by linarith
  have hCard := paddingBinIndices_card_linear L η hLone hη hηone
  have hsum : (∑ j ∈ paddingBinIndices L η, |keptCenteredBinForm data L W η j|) ≤
      (paddingBinIndices L η).card * (4*S/L*B + 4*E/L) := by
    apply (sum_le_sum (hbound N hNlog hLength hLone)).trans_eq
    simp only [sum_const,nsmul_eq_mul]
    dsimp only [S,B,E,data,η,J]
    ring
  have hCost : (∑ j ∈ paddingBinIndices L η, |keptCenteredBinForm data L W η j|) ≤
      404*S*B/η + 404*E/η := by
    apply hsum.trans
    have hc := mul_le_mul_of_nonneg_right hCard
      (by dsimp only [B,E]; positivity : 0 ≤ 4*S/L*B + 4*E/L)
    convert hc using 1 <;> field_simp <;> ring
  have hsqrt : 0 < Real.sqrt W := Real.sqrt_pos.mpr (by linarith)
  have hratio : (((3 : ℝ)^(170 : ℕ))*Real.sqrt W)^J ≤
      V * (((3 : ℝ)^(170 : ℕ))/Real.sqrt W)^J := by
    have he : W * (((3 : ℝ)^(170 : ℕ))/Real.sqrt W) = ((3 : ℝ)^(170 : ℕ))*Real.sqrt W := by
      field_simp
      nlinarith [Real.sq_sqrt (by linarith : 0 ≤ W)]
    have hm := mul_le_mul_of_nonneg_right hWV
      (by positivity : 0 ≤ (((3 : ℝ)^(170 : ℕ))/Real.sqrt W)^J)
    rw [← mul_pow,he] at hm
    exact hm
  have hGood : S*B/η ≤ S*V*η := by
    have hSpec := spectral_error_decay J
    have hnum := mul_le_mul_of_nonneg_left hratio (Real.exp_pos (5*J)).le
    have hscale : Real.exp (4*J)/η = Real.exp (5*J) := by
      dsimp only [η]
      rw [Real.exp_neg,div_eq_mul_inv,inv_inv,← Real.exp_add]
      congr 1
      ring
    have hM := mul_le_mul_of_nonneg_left hSpec hV.le
    have ht : Real.exp (5*J) * (((3 : ℝ)^(170 : ℕ))*Real.sqrt W)^J ≤ V*η := by
      apply hnum.trans
      convert hM using 1 <;> ring
    have hs := mul_le_mul_of_nonneg_left ht hS.le
    have hid : S*B/η = S*Real.exp (5*J)*(((3 : ℝ)^(170 : ℕ))*Real.sqrt W)^J := by
      dsimp only [B]
      calc
        _ = S*(Real.exp (4*J)/η)*(((3 : ℝ)^(170 : ℕ))*Real.sqrt W)^J := by ring
        _ = _ := by rw [hscale]
    rw [hid]
    convert hs using 1 <;> ring
  have hBad : 404*E/η ≤ η := by
    have he : 404*E/η = 404*Real.exp (5*J)*(8*W)^J*(5 : ℝ)^(400*Real.log L)*
        Real.exp (-(2*⌊L⌋₊ : ℕ)) := by
      dsimp only [E,η]
      rw [Real.exp_neg (J : ℝ),div_eq_mul_inv,inv_inv]
      have hh : Real.exp (4*J)*Real.exp (J : ℝ) = Real.exp (5*J) := by rw [← Real.exp_add]; congr 1; ring
      calc
        _ = 404*(Real.exp (4*J)*Real.exp (J : ℝ))*(8*W)^J*(5 : ℝ)^(400*Real.log L)*
          Real.exp (-(2*⌊L⌋₊ : ℕ)) := by ring
        _ = _ := by rw [hh]
    rw [he]
    exact hbad
  have hSV : 1 ≤ S*V := by
    simpa only [one_mul] using mul_le_mul hSone hVone zero_le_one hS.le
  have hBadSV : η ≤ S*V*η := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hSV hη.le
  have hGood404 := mul_le_mul_of_nonneg_left hGood (by norm_num : (0 : ℝ) ≤ 404)
  change (∑ j ∈ paddingBinIndices L η, |keptCenteredBinForm data L W η j|) ≤ 405*S*V*η
  have hGood404' : 404*S*B/η ≤ 404*S*V*η := by convert hGood404 using 1 <;> ring
  calc
    _ ≤ 404*S*B/η + 404*E/η := hCost
    _ ≤ 404*S*V*η + S*V*η := add_le_add hGood404' (hBad.trans hBadSV)
    _ = _ := by ring

#print axioms explicit_actual_kept_total
end ReflectedLiouville
