import ReflectedLiouville.BinSliceScales

set_option autoImplicit false
set_option maxHeartbeats 800000
open Filter
open scoped BigOperators Classical
open OAI.TwoPointCorrelations

namespace ReflectedLiouville

/-- Every fixed complementary tuple yields a literal rough reflected
    convolution. The remaining assumptions are finite supply geometry. -/
theorem reflected_slice_saving (h_KMT : KMTInput) (h_MRT : MRTRealTwistRepulsionInput)
    (A : ℕ) (hA : 1000 ≤ A) :
    ∃ C L₀ : ℝ, 0 < C ∧ 1 ≤ L₀ ∧ ∃ N₀ : ℕ, 3 ≤ N₀ ∧
      ∀ L : ℝ, L₀ ≤ L → ∀ N : ℕ, N₀ ≤ N → Real.log (N : ℝ) = L ^ A →
        ∀ (J : ℕ) (P : Fin J → Finset ℕ),
          (∀ j, ∀ p ∈ P j, p.Prime) →
          (∀ j k, k ≠ j → Disjoint (P j) (P k)) →
          (∀ j, (P j).Nonempty) →
          (∀ j, ∀ p ∈ P j, Real.exp (L ^ convolutionSizeExponent) ≤ (p : ℝ)) →
          (∀ d ∈ primeTupleDivisors P, (d : ℝ) ≤ Real.exp (2 * L)) →
          ∀ (I : Finset (Fin J)), I.Nonempty → ∀ (q : ℕ), 0 < q →
          ∀ (S : Finset (ℕ × ℕ)) (η : ℝ), 0 < η → η ≤ 1 / 2 → ∀ j : ℤ,
          ∀ y : (k : {k // k ∉ I}) → P k,
            let Z := (primeTupleSlice P I).filter (fun z => binPairEligible S η j ((∏ k, (y k).val) * z) q)
            let Y := reflectionBinCutoff N η j / ((q * ∏ k, (y k).val : ℕ) : ℝ)
            ‖∑ z ∈ Z, (z : ℂ)⁻¹ * ∑ m ∈ Finset.Icc 1 ⌊Y⌋₊,
              liouville m * liouville (N * z - m)‖ / Y ≤
                C * L ^ (-1 - convolutionFinalExponent) := by
  obtain ⟨C, L₁, hC, hL₁, N₀, hN₀, hb⟩ := reflected_rough_convolution_saving h_KMT h_MRT A hA
  have hH := (Real.tendsto_exp_atTop.comp
    (tendsto_rpow_atTop (by norm_num [convolutionSizeExponent] : 0 < convolutionSizeExponent))).eventually
      (eventually_ge_atTop (2 : ℝ))
  obtain ⟨L₂, hL₂⟩ := eventually_atTop.mp hH
  refine ⟨C, max L₁ (max 1 L₂), hC, (le_max_left 1 L₂).trans (le_max_right _ _), N₀, hN₀, ?_⟩
  intro L hL N hN hlog J P hprime hdisjoint hne hlarge hfull I hI q hq S η hη hηsmall j y
  dsimp only
  let t := ∏ k : {k // k ∉ I}, (y k).val
  let Z := (primeTupleSlice P I).filter (fun z => binPairEligible S η j (t * z) q)
  let Y := reflectionBinCutoff N η j / ((q * t : ℕ) : ℝ)
  change ‖∑ z ∈ Z, (z : ℂ)⁻¹ * ∑ m ∈ Finset.Icc 1 ⌊Y⌋₊,
    liouville m * liouville (N * z - m)‖ / Y ≤ _
  have hNpos : 0 < N := by omega
  have hLone : 1 ≤ L := (le_max_left 1 L₂).trans ((le_max_right _ _).trans hL)
  have hHtwo : 2 ≤ Real.exp (L ^ convolutionSizeExponent) := hL₂ L
    ((le_max_right 1 L₂).trans ((le_max_right _ _).trans hL))
  have ht : 0 < t := Finset.prod_pos (fun k _ => (hprime k _ (y k).property).pos)
  by_cases hZ : Z.Nonempty
  · have hrange (z : ℕ) (hz : z ∈ Z) :
        Real.exp (L ^ convolutionSizeExponent) ≤ (z : ℝ) ∧ Y / N ≤ (z : ℝ) ∧
          (z : ℝ) < 2 * (Y / N) ∧ (z : ℝ) ≤ Real.exp (2 * L) := by
      obtain ⟨hslice, hbin⟩ := Finset.mem_filter.mp hz
      have hwin := reflected_bin_slice_window S N q t z hNpos hq ht
        (primeTupleSlice_pos P I hprime hslice) η hη hηsmall j hbin
      refine ⟨primeTupleSlice_lower P I hprime _ hlarge hI hslice, hwin.1, hwin.2, ?_⟩
      exact primeTupleSlice_le_full_bound P I hprime hne _ hfull hslice
    obtain ⟨hDlow, hDhigh, hYlow, hYhigh, hdyadic⟩ := ceiling_dyadic_slice N hNpos Y
      (Real.exp (L ^ convolutionSizeExponent)) (Real.exp (2 * L)) Z hZ hHtwo hrange
    have hrough (z : ℕ) (hz : z ∈ Z) : HasNoPrimeFactorBelow (Real.exp (L ^ convolutionRoughExponent)) z := by
      apply prime_slice_no_small_factor P I hprime _ _ z (Finset.mem_filter.mp hz).1
      intro k p hp
      have hpow := Real.rpow_le_rpow_of_exponent_le hLone
        (by norm_num [convolutionRoughExponent, convolutionSizeExponent] : convolutionRoughExponent ≤ convolutionSizeExponent)
      exact (Real.exp_le_exp.mpr hpow).trans (hlarge k p hp)
    have he := hb L ((le_max_left _ _).trans hL) N hN hlog ⌈Y / N⌉₊ Y
      (by nlinarith only [hDlow]) hDhigh hYlow hYhigh Z (fun _ => 1)
      (fun z hz => ⟨(hdyadic z hz).1, (hdyadic z hz).2, hrough z hz⟩) (fun _ _ => by norm_num)
    have hid : (∑ z ∈ Z, (z : ℂ)⁻¹ * ∑ m ∈ Finset.Icc 1 ⌊Y⌋₊,
        liouville m * liouville (N * z - m)) =
        ∑ m ∈ Finset.Icc 1 ⌊Y⌋₊, ∑ z ∈ Z,
          ((1 : ℂ) / z) * liouville m * liouville (N * z - m) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro z hz
      simp only [one_div, mul_assoc]
    rw [hid]
    exact he
  · have he : Z = ∅ := Finset.not_nonempty_iff_eq_empty.mp hZ
    simp only [he, Finset.sum_empty, norm_zero, zero_div]
    positivity

#print axioms reflected_slice_saving
end ReflectedLiouville
