import ReflectedLiouville.ProgressionCardBound
import ReflectedLiouville.WindowIntegrability

set_option autoImplicit false
open MeasureTheory
open scoped BigOperators

namespace ReflectedLiouville

lemma allResidueSquares_trivial_bound (q : ℕ) [NeZero q] (x H : ℝ) (hx : 0 ≤ x) (hH : 0 ≤ H) :
    allResidueSquares q x H ≤ (q : ℝ) * (H / q + 2) ^ (2 : ℕ) := by
  unfold allResidueSquares
  calc
    _ ≤ ∑ _a : ZMod q, (H / q + 2) ^ (2 : ℕ) := by
      apply Finset.sum_le_sum
      intro a ha
      exact pow_le_pow_left₀ (norm_nonneg _) (short_progression_norm_card_bound liouville norm_liouville_le q a x H hx hH) 2
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]

theorem initial_short_energy_bound (q : ℕ) [NeZero q] (H : ℝ) (hH : 0 ≤ H) :
    (∫ x in (0 : ℝ)..H, allResidueSquares q x H) ≤ H * (q : ℝ) * (H / q + 2) ^ (2 : ℕ) := by
  have hInt := allResidueSquares_intervalIntegrable_on q 0 H H hH hH
  have hconst : IntervalIntegrable (fun _x : ℝ => (q : ℝ) * (H / q + 2) ^ (2 : ℕ)) volume 0 H :=
    intervalIntegrable_const
  have h := intervalIntegral.integral_mono_on hH hInt hconst (fun x hx =>
    allResidueSquares_trivial_bound q x H hx.1 hH)
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at h
  convert h using 1 <;> ring

lemma initial_short_energy_bound_of_ratio (q : ℕ) [NeZero q] (H : ℝ)
    (hH : 0 ≤ H) (hR : 1 ≤ H / q) :
    (∫ x in (0 : ℝ)..H, allResidueSquares q x H) ≤ 9 * H ^ (3 : ℕ) / q := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hC : H / q + 2 ≤ 3 * (H / q) := by linarith
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ H / q + 2) hC 2
  have hmul := mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ H * (q : ℝ))
  apply (initial_short_energy_bound q H hH).trans
  convert hmul using 1 <;> field_simp <;> ring

#print axioms initial_short_energy_bound_of_ratio

end ReflectedLiouville
