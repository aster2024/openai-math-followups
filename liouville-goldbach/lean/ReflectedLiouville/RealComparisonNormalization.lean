import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

set_option autoImplicit false
open scoped BigOperators

namespace ReflectedLiouville

/-- Transfer an actual integer-prefix comparison to the paper's real
    denominator, including its precise missing fractional endpoint cost. -/
theorem real_cutoff_comparison_bound (S m T ε B : ℝ) (hT : 1 ≤ T)
    (hε : 0 ≤ ε) (hB : 0 ≤ B)
    (hcmp : |S / (⌊T⌋₊ : ℝ) - m| ≤ ε) (hm : |m| ≤ B) :
    |S / T - m| ≤ ε + B / T := by
  let U := (⌊T⌋₊ : ℝ)
  have hTp : 0 < T := by linarith
  have hU1 : 1 ≤ U := by
    have hfloor : 1 ≤ ⌊T⌋₊ := Nat.le_floor (by simpa only [Nat.cast_one] using hT)
    dsimp only [U]
    exact_mod_cast hfloor
  have hUp : 0 < U := by linarith
  have hUT : U ≤ T := Nat.floor_le (by linarith)
  have hgap : T - U ≤ 1 := by have hf := Nat.lt_floor_add_one T; dsimp only [U]; linarith
  have hratio : U / T ≤ 1 := (div_le_one hTp).mpr hUT
  have hratio0 : 0 ≤ U / T := div_nonneg hUp.le hTp.le
  have hgap0 : 0 ≤ (T - U) / T := div_nonneg (sub_nonneg.mpr hUT) hTp.le
  have hgap1 : (T - U) / T ≤ 1 / T := div_le_div_of_nonneg_right hgap hTp.le
  have hid : S / T - m = (U / T) * (S / U - m) - ((T - U) / T) * m := by
    field_simp [hTp.ne', hUp.ne']
    <;> ring
  rw [hid]
  calc
    _ ≤ |(U / T) * (S / U - m)| + |((T - U) / T) * m| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        abs_add_le ((U / T) * (S / U - m)) (-(((T - U) / T) * m))
    _ = (U / T) * |S / U - m| + ((T - U) / T) * |m| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hratio0, abs_of_nonneg hgap0]
    _ ≤ (U / T) * ε + ((T - U) / T) * B := add_le_add
      (mul_le_mul_of_nonneg_left hcmp hratio0) (mul_le_mul_of_nonneg_left hm hgap0)
    _ ≤ 1 * ε + (1 / T) * B := add_le_add
      (mul_le_mul_of_nonneg_right hratio hε) (mul_le_mul_of_nonneg_right hgap1 hB)
    _ = _ := by ring

theorem real_cutoff_family_comparison {ι : Type*} (I : Finset ι)
    (S m T ε B : ι → ℝ)
    (hT : ∀ i ∈ I, 1 ≤ T i) (hε : ∀ i ∈ I, 0 ≤ ε i) (hB : ∀ i ∈ I, 0 ≤ B i)
    (hcmp : ∀ i ∈ I, |S i / (⌊T i⌋₊ : ℝ) - m i| ≤ ε i)
    (hm : ∀ i ∈ I, |m i| ≤ B i) :
    |(∑ i ∈ I, S i / T i) - (∑ i ∈ I, m i)| ≤
      (∑ i ∈ I, ε i) + ∑ i ∈ I, B i / T i := by
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  have hb := Finset.sum_le_sum (fun i hi => real_cutoff_comparison_bound (S i) (m i) (T i) (ε i) (B i)
    (hT i hi) (hε i hi) (hB i hi) (hcmp i hi) (hm i hi))
  simpa only [Finset.sum_add_distrib] using hb

#print axioms real_cutoff_family_comparison

end ReflectedLiouville
