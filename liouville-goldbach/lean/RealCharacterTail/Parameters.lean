import RealCharacterTail.Growth

set_option autoImplicit false
open scoped Topology
open Set Filter

namespace RealCharacterTail

noncomputable def parameterConstant : ℝ := Real.log 60 + 6

lemma parameterConstant_pos : 0 < parameterConstant := by
  have h := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 60)
  dsimp [parameterConstant]
  linarith

/-- Only eventual elementary size conditions on X are needed. -/
theorem eventually_cutoff_range : ∀ᶠ X : ℝ in atTop,
    100 ≤ X ∧ 2 ≤ Real.log X ∧ 2 ≤ (Real.log X) ^ (64 : ℕ) ∧
      (Real.log X) ^ (64 : ℕ) ≤ X := by
  have hlog : ∀ᶠ X : ℝ in atTop, 2 ≤ Real.log X :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 2)
  have hratio : ∀ᶠ X : ℝ in atTop, (Real.log X) ^ (64 : ℕ) / X < 1 := by
    have ht := Real.tendsto_pow_log_div_mul_add_atTop 1 0 64 (by norm_num)
    simpa using ht.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [eventually_ge_atTop (100 : ℝ), hlog, hratio] with X hX hl hr
  have hXp : 0 < X := by linarith
  have hY : 2 ≤ (Real.log X) ^ (64 : ℕ) :=
    (by norm_num : (2 : ℝ) ≤ 2 ^ (64 : ℕ)).trans
      (pow_le_pow_left₀ (by norm_num) hl 64)
  exact ⟨hX, hl, hY, ((div_lt_one hXp).mp hr).le⟩

lemma height_log_bound {q : ℕ} [NeZero q] {X : ℝ}
    (hX : 100 ≤ X) (hlog : 2 ≤ Real.log X) (hqX : (q : ℝ) ≤ X) :
    Real.log (20 * (q : ℝ) * (X ^ 4 + 2)) + 1 ≤ parameterConstant * Real.log X := by
  have hXp : 0 < X := by linarith
  have hq : 0 < (q : ℝ) := Nat.cast_pos.mpr (NeZero.pos q)
  have h4 : 1 ≤ X ^ 4 := one_le_pow₀ (by linarith : 1 ≤ X)
  have hsize : 20 * (q : ℝ) * (X ^ 4 + 2) ≤ 60 * X ^ 5 := by
    calc
      _ ≤ 20 * X * (X ^ 4 + 2) := by gcongr
      _ ≤ 20 * X * (3 * X ^ 4) := by gcongr; linarith
      _ = _ := by ring
  have hl := Real.log_le_log (by positivity : 0 < 20 * (q : ℝ) * (X ^ 4 + 2)) hsize
  rw [Real.log_mul (by norm_num : (60 : ℝ) ≠ 0) (pow_ne_zero 5 hXp.ne'), Real.log_pow] at hl
  norm_num at hl
  have h60 : 0 ≤ Real.log 60 := Real.log_nonneg (by norm_num)
  have hm := mul_nonneg (by linarith : 0 ≤ Real.log X - 1) (by linarith : 0 ≤ Real.log 60 + 1)
  dsimp [parameterConstant]
  nlinarith

lemma cutoff_power_saving {X x : ℝ} (hlog : 2 ≤ Real.log X)
    (hyx : (Real.log X) ^ (64 : ℕ) ≤ x) :
    Real.log X * x ^ (-1 / 16 : ℝ) ≤ 1 := by
  have hlp : 0 < Real.log X := by linarith
  have hYp : 0 < (Real.log X) ^ (64 : ℕ) := pow_pos hlp _
  have hr : x ^ (-1 / 16 : ℝ) ≤ ((Real.log X) ^ (64 : ℕ)) ^ (-1 / 16 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos hYp hyx (by norm_num)
  have he : ((Real.log X) ^ (64 : ℕ)) ^ (-1 / 16 : ℝ) =
      (Real.log X) ^ (-4 : ℝ) := by
    rw [← Real.rpow_natCast_mul hlp.le 64 (-1 / 16)]
    norm_num
  rw [he] at hr
  calc
    _ ≤ Real.log X * (Real.log X) ^ (-4 : ℝ) := mul_le_mul_of_nonneg_left hr hlp.le
    _ = (Real.log X) ^ (-3 : ℝ) := by
      conv_lhs => lhs; rw [← Real.rpow_one (Real.log X)]
      rw [← Real.rpow_add hlp]
      norm_num
    _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)

lemma height_power_saving {X x : ℝ} (hX : 100 ≤ X) (hx : 0 ≤ x) (hxX : x ≤ X) :
    Real.log X * (x ^ 2 / X ^ 4) ≤ 1 := by
  have hXp : 0 < X := by linarith
  have hlog : Real.log X ≤ X ^ 2 :=
    (Real.log_le_self hXp.le).trans (by nlinarith)
  have hs : x ^ 2 ≤ X ^ 2 := (sq_le_sq₀ hx hXp.le).mpr hxX
  have hm := mul_le_mul hlog hs (sq_nonneg x) (sq_nonneg X)
  rw [← mul_div_assoc]
  apply (div_le_one (pow_pos hXp 4)).mpr
  nlinarith

/-- The parameter choice closes the uniform analytic error at either endpoint. -/
theorem parameter_error_bound {q : ℕ} [NeZero q] {X x : ℝ}
    (hX : 100 ≤ X) (hlog : 2 ≤ Real.log X) (hqX : (q : ℝ) ≤ X)
    (hx : 0 ≤ x) (hyx : (Real.log X) ^ (64 : ℕ) ≤ x) (hxX : x ≤ X) :
    (Real.log (20 * (q : ℝ) * (X ^ 4 + 2)) + 1) *
      (x ^ (-1 / 16 : ℝ) + x ^ 2 / X ^ 4) ≤ 2 * parameterConstant := by
  have hK := parameterConstant_pos.le
  have hb := height_log_bound hX hlog hqX
  have hfirst := cutoff_power_saving hlog hyx
  have hsecond := height_power_saving hX hx hxX
  calc
    _ ≤ (parameterConstant * Real.log X) * (x ^ (-1 / 16 : ℝ) + x ^ 2 / X ^ 4) :=
      mul_le_mul_of_nonneg_right hb (by positivity)
    _ = parameterConstant * (Real.log X * x ^ (-1 / 16 : ℝ) +
        Real.log X * (x ^ 2 / X ^ 4)) := by ring
    _ ≤ parameterConstant * (1 + 1) :=
      mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond) hK
    _ = _ := by ring

#print axioms eventually_cutoff_range
#print axioms parameter_error_bound

end RealCharacterTail
