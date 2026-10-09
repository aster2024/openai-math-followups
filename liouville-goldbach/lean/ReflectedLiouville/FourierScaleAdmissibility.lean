import ReflectedLiouville.FourierPowerMargins

set_option autoImplicit false
open Filter

namespace ReflectedLiouville

lemma eventually_log_power_gap (a b C : ℝ) (hab : a < b) :
    ∀ᶠ N : ℝ in atTop, C * (Real.log N) ^ a ≤ (Real.log N) ^ b := by
  have hlim := (tendsto_rpow_atTop (sub_pos.mpr hab)).comp Real.tendsto_log_atTop
  filter_upwards [hlim.eventually (eventually_ge_atTop C),
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with N hC hlog
  have hmul := mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hlog.le a)
  have hid : (Real.log N) ^ (b - a) * (Real.log N) ^ a = (Real.log N) ^ b := by
    rw [← Real.rpow_add hlog]
    congr 1
    ring
  change C * (Real.log N) ^ a ≤ (Real.log N) ^ (b - a) * (Real.log N) ^ a at hmul
  rwa [hid] at hmul

/-- Uniform variance-height condition in the complete D range. -/
theorem eventually_fourier_scale_admissible (ν₀ : ℝ) (hν : 0 < ν₀) :
    ∀ᶠ N : ℝ in atTop, ∀ D : ℝ,
      Real.exp ((Real.log N) ^ ν₀) ≤ D → D ≤ N → 1 < D →
      Real.log D / 8 ≤ Real.log (⌊D ^ (1 / 4 : ℝ)⌋₊ : ℝ) →
      Real.exp ((Real.log (N * (⌊D⌋₊ : ℝ))) ^ (ν₀ / 2)) ≤
        (⌊D ^ (1 / 4 : ℝ)⌋₊ : ℝ) := by
  filter_upwards [eventually_log_power_gap (ν₀ / 2) ν₀ (8 * (2 : ℝ) ^ (ν₀ / 2)) (by linarith),
    eventually_ge_atTop (2 : ℝ)] with N hgap hN
  intro D hDlow hDN hD hlogM
  have hNp : 0 < N := by linarith
  have hDp : 0 < D := by linarith
  have hKp : (0 : ℝ) < ⌊D⌋₊ := by
    have hK : 1 ≤ ⌊D⌋₊ := Nat.le_floor (by simpa only [Nat.cast_one] using hD.le)
    exact_mod_cast (show 0 < ⌊D⌋₊ by omega)
  have hKhi : (⌊D⌋₊ : ℝ) ≤ N := (Nat.floor_le hDp.le).trans hDN
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have hNK1 : 1 ≤ N * (⌊D⌋₊ : ℝ) := by
    have hK1 : (1 : ℝ) ≤ ⌊D⌋₊ := by exact_mod_cast Nat.le_floor (by simpa only [Nat.cast_one] using hD.le)
    nlinarith
  have hNKp : 0 < N * (⌊D⌋₊ : ℝ) := mul_pos hNp hKp
  have hlogNK : Real.log (N * (⌊D⌋₊ : ℝ)) ≤ 2 * Real.log N := by
    have h := Real.log_le_log hKp hKhi
    rw [Real.log_mul hNp.ne' hKp.ne']
    linarith
  have hpow := Real.rpow_le_rpow (Real.log_nonneg hNK1) hlogNK (by linarith : 0 ≤ ν₀ / 2)
  have hDlog : (Real.log N) ^ ν₀ ≤ Real.log D := by
    have h := Real.log_le_log (Real.exp_pos _) hDlow
    rwa [Real.log_exp] at h
  have hbase : (2 * Real.log N) ^ (ν₀ / 2) ≤ Real.log D / 8 := by
    rw [Real.mul_rpow (by norm_num) hlogN]
    linarith
  have hpowM := hpow.trans (hbase.trans hlogM)
  have hMpos : (0 : ℝ) < ⌊D ^ (1 / 4 : ℝ)⌋₊ := by
    have hpow1 : 1 ≤ D ^ (1 / 4 : ℝ) := by
      simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hD.le (by norm_num : (0 : ℝ) ≤ 1 / 4)
    exact_mod_cast (show 0 < ⌊D ^ (1 / 4 : ℝ)⌋₊ by have hfloor : 1 ≤ ⌊D ^ (1 / 4 : ℝ)⌋₊ := Nat.le_floor (by simpa only [Nat.cast_one] using hpow1); omega)
  have h := Real.exp_le_exp.mpr hpowM
  rwa [Real.exp_log hMpos] at h

#print axioms eventually_fourier_scale_admissible

end ReflectedLiouville
