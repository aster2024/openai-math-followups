import ReflectedLiouville.ActualKeptPairing

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Filter
open scoped BigOperators Classical
open OAI.TwoPointCorrelations

namespace ReflectedLiouville

theorem actual_kept_bin_bound (W δ : ℝ) (hW : 1 ≤ W) (hδ : 0 < δ) (hδsmall : δ ≤ 1/200) :
    ∃ Af : ℕ, 1000 ≤ Af ∧ ∀ a : ℝ, ∀ᶠ L : ℝ in atTop,
      ∀ (N : ℕ) [NeZero N], Real.log (N : ℝ) ≤ L ^ a → Real.exp (L ^ Af / 2) ≤ (N : ℝ) →
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
  obtain ⟨Af,hAf,hb⟩ := kept_operator_bilinear_bound W δ hW hδ hδsmall
  refine ⟨Af,hAf,?_⟩
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

#print axioms actual_kept_bin_bound
end ReflectedLiouville
