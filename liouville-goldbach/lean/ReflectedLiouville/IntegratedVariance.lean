import ReflectedLiouville.AllProgressionVariance
import ReflectedLiouville.DyadicIntegral
import ReflectedLiouville.InitialEnergy

set_option autoImplicit false
open MeasureTheory
open scoped BigOperators

namespace ReflectedLiouville

/-- Full initial-to-Y energy: small origins use the proved trivial bound and
    all remaining origins use the KMT-derived dyadic variance. -/
theorem initial_to_length_variance
    (h_KMT : KMTInput) (h_MRT : MRTRealTwistRepulsionInput) :
    ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∃ C X₀ : ℝ, 0 < C ∧ 10 ≤ X₀ ∧
      ∀ (q : ℕ) [NeZero q] (Y H : ℝ), X₀ ≤ H → H ≤ Y → 10 * (q : ℝ) ≤ H →
        Real.exp ((Real.log Y) ^ ν) ≤ H / q →
        (∫ x in (0 : ℝ)..Y, allResidueSquares q x H) ≤
          9 * H ^ (3 : ℕ) / q + 2 * C * Y * H ^ (2 : ℕ) / q /
            Real.rpow (Real.log (H / q)) (1 / 1000) := by
  intro ν hν hν₁
  obtain ⟨C, X₀, hC, hX₀, hvariance⟩ := liouville_short_progression_variance h_KMT h_MRT ν hν hν₁
  refine ⟨C, X₀, hC, hX₀, ?_⟩
  intro q inst Y H hH₀ hHY hHq hRlarge
  have hH10 : 10 ≤ H := hX₀.trans hH₀
  have hH : 0 < H := by linarith
  have hY : 0 < Y := hH.trans_le hHY
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hR10 : 10 ≤ H / q := (le_div_iff₀ hq).mpr hHq
  have hR : 1 ≤ H / q := by linarith
  have hlogR : 0 < Real.log (H / q) := Real.log_pos (by linarith)
  let F := fun x : ℝ => allResidueSquares q x H
  let B := C * H ^ (2 : ℕ) / q / Real.rpow (Real.log (H / q)) (1 / 1000)
  have hB : 0 ≤ B := by
    dsimp only [B]
    exact div_nonneg (div_nonneg (mul_nonneg hC.le (sq_nonneg H)) hq.le)
      (Real.rpow_nonneg hlogR.le _)
  have hInt : ∀ A Z : ℝ, A ≤ Z → IntervalIntegrable F volume A Z :=
    fun A Z hAZ => allResidueSquares_intervalIntegrable_on q A Z H hAZ hH.le
  have hf : ∀ x : ℝ, 0 ≤ F x := by
    intro x
    exact Finset.sum_nonneg (fun a _ => sq_nonneg _)
  have hcell : ∀ X : ℝ, H ≤ X → X ≤ Y → (∫ x in X..2 * X, F x) ≤ B * X := by
    intro X hHX hXY
    have hXp : 0 < X := hH.trans_le hHX
    have hX₁ : 1 ≤ X := by linarith
    have hlogXY := Real.log_le_log hXp hXY
    have hpow := Real.rpow_le_rpow (Real.log_nonneg hX₁) hlogXY hν.le
    have hRlargeX := (Real.exp_le_exp.mpr hpow).trans hRlarge
    have hv := hvariance q X H (hH₀.trans hHX) hHX hHq hRlargeX
    change (∫ x in X..2 * X, F x) ≤ _ at hv
    convert hv using 1 <;> dsimp only [B] <;> ring
  have hhigh := dyadic_integral_upper F H Y B hH hHY hB hInt hf hcell
  have hlow := initial_short_energy_bound_of_ratio q H hH.le hR
  have hsum := intervalIntegral.integral_add_adjacent_intervals (hInt 0 H hH.le) (hInt H Y hHY)
  change (∫ x in (0 : ℝ)..H, F x) + (∫ x in H..Y, F x) = (∫ x in (0 : ℝ)..Y, F x) at hsum
  rw [← hsum]
  have h := add_le_add hlow hhigh
  convert h using 1 <;> dsimp only [B] <;> ring

#print axioms initial_to_length_variance

end ReflectedLiouville
