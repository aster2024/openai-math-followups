import ReflectedLiouville.BinnedDilation

set_option autoImplicit false
open Filter
open scoped BigOperators Classical
open OAI.TwoPointCorrelations

namespace ReflectedLiouville

lemma reflection_pair_eligible (N : ℕ) [NeZero N] (W δ L η : ℝ)
    (hL : 1 ≤ L) (hW : 0 ≤ W) (dq : ℕ × ℕ)
    (hdq : dq ∈ (reflectionPrimeFamily N W δ L η hL hW).pairs) :
    PaddingPairEligible L η dq.1 dq.2 := (mem_primeFamilyPairs.mp hdq).2.2.2

lemma exp_negative_count_le_half (J : ℕ) (hJ : 1 ≤ J) : Real.exp (-(J : ℝ)) ≤ 1 / 2 := by
  have hJr : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  calc
    _ ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
    _ = 1 / Real.exp 1 := by rw [Real.exp_neg, one_div]
    _ ≤ _ := div_le_div_of_nonneg_left zero_le_one (by norm_num) Real.exp_one_gt_two.le

/-- The literal raw-bin dilation and mass bounds for the constructed family.
    This is the main theorem's deterministic bridge to the reflected sum. -/
theorem actual_raw_bins_dilation (a W δ : ℝ) (hW : 1 ≤ W) (hδ : 0 < δ) (hδ₁ : δ < 1) :
    ∀ᶠ L : ℝ in atTop, ∀ (N : ℕ) [NeZero N], Real.log (N : ℝ) ≤ L ^ a →
      ∀ hL : 1 ≤ L,
        let J := reflectionBandCount W δ L
        let η := Real.exp (-(J : ℝ))
        let data := reflectionPrimeFamily N W δ L η hL (by linarith)
        let P := centeredPrimeBands N.primeFactors (L ^ (1 - δ)) W J
        let V := ∏ j, primeHarmonicMass (P j)
        let S := paddingTiltNormalizer data.Q
        let S₀ := retainedPairMass data.pairs
        |(∑ j ∈ paddingBinIndices L η, rawBinForm data.pairs N η j) - S₀ * (reflectedSum N / N)| ≤
          (4 * η + 2 / N) * S * V ∧ (1 / 2 : ℝ) * S * V ≤ S₀ ∧ S₀ ≤ S * V := by
  filter_upwards [retained_padding_mass W δ a hW hδ hδ₁,
    eventually_reflectionBandCount_positive W δ (by linarith) hδ,
    eventually_ge_atTop (1 : ℝ)] with L hmass hJ hL₀
  intro N inst hN hL
  dsimp only
  let J := reflectionBandCount W δ L
  let η := Real.exp (-(J : ℝ))
  let data := reflectionPrimeFamily N W δ L η hL (by linarith : 0 ≤ W)
  let P := centeredPrimeBands N.primeFactors (L ^ (1 - δ)) W J
  let V := ∏ j, primeHarmonicMass (P j)
  let S := paddingTiltNormalizer data.Q
  let S₀ := retainedPairMass data.pairs
  have hη : 0 < η := Real.exp_pos _
  have hηhalf : η ≤ 1 / 2 := exp_negative_count_le_half J hJ
  have hgeom := reflection_tuple_geometry N W δ L hW hδ.le hL
  have hI : data.pairs ⊆ (primeTupleDivisors P) ×ˢ retainedPrimeDivisors data.Q := by
    intro dq hdq
    have hm := mem_primeFamilyPairs.mp hdq
    exact Finset.mem_product.mpr ⟨hm.1, hm.2.1⟩
  have hpositive : ∀ dq ∈ data.pairs, 0 < dq.1 * dq.2 := by
    intro dq hdq
    exact Nat.mul_pos (Nat.pos_of_ne_zero (data.tuple_squarefree _ hdq).ne_zero)
      (Nat.pos_of_ne_zero (data.padding_squarefree _ hdq).ne_zero)
  have hcover : ∀ dq ∈ data.pairs, reflectionPairBin η dq ∈ paddingBinIndices L η := by
    intro dq hdq
    exact (reflection_pair_eligible N W δ L η hL (by linarith) dq hdq).2
  have hupper : S₀ ≤ S * V := by
    have hb := retainedPairMass_le_product_mass data.pairs (primeTupleDivisors P) data.Q data.primeQ hI
    rw [hgeom.2] at hb
    exact hb
  have hlower : (1 / 2 : ℝ) * S * V ≤ S₀ := by
    have hb := (hmass N hN η hη).2
    have hbeq : S₀ = totalPaddingBinMass (primeTupleDivisors P) data.Q L η :=
      actual_pair_mass_eq_bin_mass N W δ L η hL (by linarith) hη
    have hb' : (1 / 2 : ℝ) * S * V ≤ totalPaddingBinMass (primeTupleDivisors P) data.Q L η := hb
    rwa [← hbeq] at hb'
  refine ⟨?_, hlower, hupper⟩
  rw [raw_bin_forms_sum data.pairs (paddingBinIndices L η) N η hcover]
  have hb := raw_bin_dilation_bound data.pairs N η (NeZero.pos N) hη hηhalf hpositive
  have hscale := mul_le_mul_of_nonneg_left hupper (by positivity : 0 ≤ 4 * η + 2 / (N : ℝ))
  apply hb.trans
  convert hscale using 1 <;> ring

#print axioms actual_raw_bins_dilation

end ReflectedLiouville
