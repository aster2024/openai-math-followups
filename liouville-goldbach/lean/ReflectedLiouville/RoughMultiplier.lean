import OAI.NumberTheory.TwoPointCorrelations.FinalMain
import OAI.NumberTheory.TwoPoint.Bounds.QualitativeRoughFourier
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false
open Filter MeasureTheory
open OAI.TwoPointCorrelations

namespace ReflectedLiouville

lemma eventually_scaled_log_power (a r s : ℝ) (hsr : s < r) :
    ∀ᶠ L : ℝ in atTop, a * Real.log L / L ^ r ≤ L ^ (-s) := by
  have hlim := (isLittleO_log_rpow_atTop (sub_pos.mpr hsr)).tendsto_div_nhds_zero
  have hlim' := (tendsto_const_nhds (x := a)).mul hlim
  filter_upwards [hlim'.eventually (eventually_le_nhds (by norm_num : a * (0 : ℝ) < 1)),
    eventually_gt_atTop (0 : ℝ)] with L hL hpos
  have hpow : 0 < L ^ (r - s) := Real.rpow_pos_of_pos hpos _
  have hmain : a * Real.log L ≤ L ^ (r - s) := by
    have hratio : a * Real.log L / L ^ (r - s) ≤ 1 := by
      simpa only [mul_div_assoc] using hL
    simpa only [one_mul] using (div_le_iff₀ hpow).mp hratio
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hpos r)).mpr
  simpa only [← Real.rpow_add hpos, sub_eq_add_neg, add_comm] using hmain

/-- A proved rough multiplier with an arbitrarily small positive exponent loss.
    This uses the existing finite four-form sieve, not an extra hypothesis. -/
theorem rough_multiplier_with_slack (γr γs κ : ℝ)
    (hγr : 0 < γr) (hγsr : γs < γr) (hκ : γr < κ) :
    ∃ U V : ℝ, 0 < U ∧ 0 < V ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (D h : ℕ), (1 / 2 : ℝ) * Real.exp (L ^ κ) ≤ D → 0 < h →
      ∀ (Z : Finset ℕ) (c : ℕ → ℂ),
        (∀ z ∈ Z, D ≤ z ∧ z < D + D ∧ HasNoPrimeFactorBelow (Real.exp (L ^ γr)) z) →
        (∀ z ∈ Z, ‖c z‖ ≤ 1) →
        (∀ θ, ‖weightedRoughFourier Z c h θ‖ ≤ U * L ^ (-γs)) ∧
        (∫ θ, ‖weightedRoughFourier Z c h θ‖ ^ 4 ∂AddCircle.haarAddCircle) ≤
          V / (D : ℝ) * L ^ (-4 * γs) := by
  obtain ⟨U, V, hU, hV, hqual⟩ := primeReciprocalInput.qualitative_rough_fourier
  let a := γr / (9999 / 10000 : ℝ)
  have ha : 0 < a := by dsimp [a]; positivity
  have hscale := (tendsto_rpow_atTop ha).eventually hqual
  refine ⟨U, V, hU, hV, ?_⟩
  filter_upwards [hscale, eventually_scaled_log_power a γr γs hγsr,
    eventually_ge_atTop (1 : ℝ)] with L hqualL hrate hL
  intro D h hD hh Z c hZ hc
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hpower : (L ^ a) ^ (9999 / 10000 : ℝ) = L ^ γr := by
    rw [← Real.rpow_mul hLp.le]
    congr 1
    dsimp [a]
    field_simp
  have hD' : (1 / 2 : ℝ) * Real.exp ((L ^ a) ^ (9999 / 10000 : ℝ)) ≤ D := by
    rw [hpower]
    apply le_trans _ hD
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (Real.rpow_le_rpow_of_exponent_le hL hκ.le)) (by norm_num)
  have hZ' : ∀ z ∈ Z, D ≤ z ∧ z < D + D ∧
      HasNoPrimeFactorBelow (Real.exp ((L ^ a) ^ (9999 / 10000 : ℝ))) z := by
    simpa only [hpower] using hZ
  obtain ⟨hbound, hfour⟩ := hqualL D h hD' hh Z c hZ' hc
  have hrate' : Real.log (L ^ a) / (L ^ a) ^ (9999 / 10000 : ℝ) ≤ L ^ (-γs) := by
    rw [hpower, Real.log_rpow hLp]
    simpa only [mul_comm a] using hrate
  refine ⟨fun θ => (hbound θ).trans (mul_le_mul_of_nonneg_left hrate' hU.le), ?_⟩
  have hnonneg : 0 ≤ Real.log (L ^ a) / (L ^ a) ^ (9999 / 10000 : ℝ) := by
    apply div_nonneg
    · exact Real.log_nonneg (Real.one_le_rpow hL ha.le)
    · positivity
  apply hfour.trans
  have hfourrate := pow_le_pow_left₀ hnonneg hrate' 4
  have heq : (L ^ (-γs)) ^ (4 : ℕ) = L ^ (-4 * γs) := by
    rw [← Real.rpow_mul_natCast hLp.le]
    congr 1
    norm_num
    ring
  rw [heq] at hfourrate
  exact mul_le_mul_of_nonneg_left hfourrate (div_nonneg hV.le (Nat.cast_nonneg D))

lemma slack_centering_margin :
    (5 : ℝ) * (99997 / 100000) + 1 / 4000 - (5 + 5 * (1 / 100000)) = 1 / 20000 := by
  norm_num

#print axioms rough_multiplier_with_slack

end ReflectedLiouville
