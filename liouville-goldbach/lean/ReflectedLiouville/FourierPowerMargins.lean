import ReflectedLiouville.RationalWindowUniform
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false
open Filter

namespace ReflectedLiouville

lemma eventually_power_le_log_saving (a b C : ℝ) (ha : 0 < a) :
    ∀ᶠ D : ℝ in atTop, C * D ^ (-a) ≤ (Real.log D) ^ (-b) := by
  have hlim := (isLittleO_log_rpow_rpow_atTop b ha).tendsto_div_nhds_zero
  have h := (tendsto_const_nhds (x := C)).mul hlim
  filter_upwards [h.eventually (eventually_le_nhds (by simp : C * (0 : ℝ) < 1)),
    eventually_gt_atTop (1 : ℝ)] with D hD hD₁
  have hDp : 0 < D := by linarith
  have hlog : 0 < Real.log D := Real.log_pos hD₁
  change C * ((Real.log D) ^ b / D ^ a) ≤ 1 at hD
  have hmul : C * (Real.log D) ^ b ≤ D ^ a := by
    have hr : C * (Real.log D) ^ b / D ^ a ≤ 1 := by simpa only [← mul_div_assoc] using hD
    simpa only [one_mul] using (div_le_iff₀ (Real.rpow_pos_of_pos hDp a)).mp hr
  rw [Real.rpow_neg hDp.le, Real.rpow_neg hlog.le, ← div_eq_mul_inv, inv_eq_one_div]
  exact (div_le_div_iff₀ (Real.rpow_pos_of_pos hDp a) (Real.rpow_pos_of_pos hlog b)).mpr (by simpa only [one_mul] using hmul)

lemma floor_ge_half (x : ℝ) (hx : 2 ≤ x) : x / 2 ≤ (⌊x⌋₊ : ℝ) := by
  have h := Nat.lt_floor_add_one x
  linarith

lemma floor_power_le_floor_power (D a b : ℝ) (hD : 1 ≤ D) (hab : a ≤ b) :
    ⌊D ^ a⌋₊ ≤ ⌊D ^ b⌋₊ := Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le hD hab)

/-- Polynomial scales supply much more slack than the logarithmic losses needed
    in the same Dirichlet/window argument. -/
theorem eventually_fourier_power_margins :
    ∀ᶠ D : ℝ in atTop,
      let K := ⌊D⌋₊
      let Q := ⌊D ^ (1 / 3 : ℝ)⌋₊
      let M := ⌊D ^ (1 / 4 : ℝ)⌋₊
      1 < D ∧ 10 ≤ M ∧ M ≤ Q ∧ Q * Q ≤ K ∧
        Real.log D / 8 ≤ Real.log (M : ℝ) ∧
        ((Q * Q : ℕ) : ℝ) / K ≤ (Real.log D) ^ (-(1 / 1000) : ℝ) ∧
        1 ≤ (M : ℝ) ^ (2 : ℕ) * (Real.log D) ^ (-(1 / 1000) : ℝ) ∧
        (M : ℝ) ^ (2 : ℕ) ≤ (Q : ℝ) ^ (2 : ℕ) * (Real.log D) ^ (-(1 / 2000) : ℝ) ∧
        ((Q * Q : ℕ) : ℝ) + 1 ≤ D * (Real.log D) ^ (-(1 / 2000) : ℝ) := by
  have hMlim := tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)
  filter_upwards [eventually_power_le_log_saving (1 / 3) (1 / 1000) 2 (by norm_num),
    eventually_power_le_log_saving (1 / 2) (1 / 1000) 4 (by norm_num),
    eventually_power_le_log_saving (1 / 6) (1 / 2000) 4 (by norm_num),
    eventually_power_le_log_saving (1 / 3) (1 / 2000) 2 (by norm_num),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (max 1 (8 * Real.log 2))),
    hMlim.eventually (eventually_ge_atTop (20 : ℝ)), eventually_ge_atTop (8 : ℝ)] with D h₁ h₂ h₃ h₄ hL hM hD8
  dsimp only
  let K := ⌊D⌋₊
  let Q := ⌊D ^ (1 / 3 : ℝ)⌋₊
  let M := ⌊D ^ (1 / 4 : ℝ)⌋₊
  have hD : 1 < D := by linarith
  have hDp : 0 < D := by linarith
  have hL1 : 1 ≤ Real.log D := (le_max_left _ _).trans hL
  have hLp : 0 < Real.log D := by linarith
  have hKlo : D / 2 ≤ (K : ℝ) := floor_ge_half D (by linarith)
  have hKp : (0 : ℝ) < K := (by positivity : 0 < D / 2).trans_le hKlo
  have hQexp : D ^ (1 / 4 : ℝ) ≤ D ^ (1 / 3 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hD.le (by norm_num)
  have hQ20 : 20 ≤ D ^ (1 / 3 : ℝ) := hM.trans hQexp
  have hQlo : D ^ (1 / 3 : ℝ) / 2 ≤ (Q : ℝ) := floor_ge_half _ (by linarith)
  have hMlo : D ^ (1 / 4 : ℝ) / 2 ≤ (M : ℝ) := floor_ge_half _ (by linarith)
  have hQhi : (Q : ℝ) ≤ D ^ (1 / 3 : ℝ) := Nat.floor_le (Real.rpow_nonneg hDp.le _)
  have hMhi : (M : ℝ) ≤ D ^ (1 / 4 : ℝ) := Nat.floor_le (Real.rpow_nonneg hDp.le _)
  have hM10 : 10 ≤ M := by exact_mod_cast (show (10 : ℝ) ≤ M by linarith)
  have hMQ : M ≤ Q := floor_power_le_floor_power D _ _ hD.le (by norm_num)
  have hQp : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hMp : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hQsqhi : (Q : ℝ) ^ (2 : ℕ) ≤ D ^ (2 / 3 : ℝ) := by
    have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ Q) hQhi 2
    rw [← Real.rpow_mul_natCast hDp.le] at hp
    norm_num at hp
    exact hp
  have hQsqlo : D ^ (2 / 3 : ℝ) / 4 ≤ (Q : ℝ) ^ (2 : ℕ) := by
    have hp := pow_le_pow_left₀ (by positivity : 0 ≤ D ^ (1 / 3 : ℝ) / 2) hQlo 2
    have hid : (D ^ (1 / 3 : ℝ) / 2) ^ (2 : ℕ) = D ^ (2 / 3 : ℝ) / 4 := by
      rw [div_pow, ← Real.rpow_mul_natCast hDp.le]; norm_num
    rwa [hid] at hp
  have hMsqlo : D ^ (1 / 2 : ℝ) / 4 ≤ (M : ℝ) ^ (2 : ℕ) := by
    have hp := pow_le_pow_left₀ (by positivity : 0 ≤ D ^ (1 / 4 : ℝ) / 2) hMlo 2
    have hid : (D ^ (1 / 4 : ℝ) / 2) ^ (2 : ℕ) = D ^ (1 / 2 : ℝ) / 4 := by
      rw [div_pow, ← Real.rpow_mul_natCast hDp.le]; norm_num
    rwa [hid] at hp
  have hMsqhi : (M : ℝ) ^ (2 : ℕ) ≤ D ^ (1 / 2 : ℝ) := by
    have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ M) hMhi 2
    rw [← Real.rpow_mul_natCast hDp.le] at hp
    norm_num at hp
    exact hp
  have he₁ : D ^ (2 / 3 : ℝ) / (D / 2) = 2 * D ^ (-(1 / 3) : ℝ) := by
    calc
      _ = 2 * (D ^ (2 / 3 : ℝ) / D) := by ring
      _ = _ := by
        conv_lhs => arg 2; arg 2; rw [← Real.rpow_one D]
        rw [← Real.rpow_sub hDp]
        norm_num
  have hratio : (Q : ℝ) ^ (2 : ℕ) / K ≤ (Real.log D) ^ (-(1 / 1000) : ℝ) := by
    calc
      _ ≤ D ^ (2 / 3 : ℝ) / (D / 2) := div_le_div₀ (Real.rpow_nonneg hDp.le _) hQsqhi (by positivity) hKlo
      _ = _ := he₁
      _ ≤ _ := h₁
  have hsavele : (Real.log D) ^ (-(1 / 1000) : ℝ) ≤ 1 := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num : (-(1 / 1000) : ℝ) ≤ 0)
  have hQK : Q * Q ≤ K := by
    have h := (div_le_iff₀ hKp).mp (hratio.trans hsavele)
    have hr : (Q : ℝ) * Q ≤ K := by simpa only [pow_two, one_mul] using h
    exact_mod_cast hr
  have hlogM : Real.log D / 8 ≤ Real.log (M : ℝ) := by
    have hl := Real.log_le_log (by positivity : 0 < D ^ (1 / 4 : ℝ) / 2) hMlo
    rw [Real.log_div (by positivity) (by norm_num), Real.log_rpow hDp] at hl
    have hL2 : 8 * Real.log 2 ≤ Real.log D := (le_max_right _ _).trans hL
    linarith
  have honesave : 1 ≤ (M : ℝ) ^ (2 : ℕ) * (Real.log D) ^ (-(1 / 1000) : ℝ) := by
    have ht := mul_le_mul_of_nonneg_right h₂ (by positivity : 0 ≤ D ^ (1 / 2 : ℝ) / 4)
    have hid : 4 * D ^ (-(1 / 2) : ℝ) * (D ^ (1 / 2 : ℝ) / 4) = 1 := by
      rw [show (4 : ℝ) * D ^ (-(1 / 2) : ℝ) * (D ^ (1 / 2 : ℝ) / 4) =
        D ^ (-(1 / 2) : ℝ) * D ^ (1 / 2 : ℝ) by ring, ← Real.rpow_add hDp]; norm_num
    rw [hid] at ht
    exact ht.trans (by simpa only [mul_comm] using mul_le_mul_of_nonneg_right hMsqlo (Real.rpow_nonneg hLp.le _))
  have hsmallsave : (M : ℝ) ^ (2 : ℕ) ≤ (Q : ℝ) ^ (2 : ℕ) * (Real.log D) ^ (-(1 / 2000) : ℝ) := by
    have ht := mul_le_mul_of_nonneg_right h₃ (by positivity : 0 ≤ D ^ (2 / 3 : ℝ) / 4)
    have hid : 4 * D ^ (-(1 / 6) : ℝ) * (D ^ (2 / 3 : ℝ) / 4) = D ^ (1 / 2 : ℝ) := by
      rw [show (4 : ℝ) * D ^ (-(1 / 6) : ℝ) * (D ^ (2 / 3 : ℝ) / 4) =
        D ^ (-(1 / 6) : ℝ) * D ^ (2 / 3 : ℝ) by ring, ← Real.rpow_add hDp]; norm_num
    rw [hid] at ht
    have hf := mul_le_mul_of_nonneg_right hQsqlo (Real.rpow_nonneg hLp.le (-(1 / 2000)))
    exact hMsqhi.trans (ht.trans (by simpa only [mul_comm] using hf))
  have hendsave : (Q : ℝ) ^ (2 : ℕ) + 1 ≤ D * (Real.log D) ^ (-(1 / 2000) : ℝ) := by
    have hp1 : 1 ≤ D ^ (2 / 3 : ℝ) := by
      simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hD.le (by norm_num : (0 : ℝ) ≤ 2 / 3)
    have ht := mul_le_mul_of_nonneg_right h₄ hDp.le
    have hid : 2 * D ^ (-(1 / 3) : ℝ) * D = 2 * D ^ (2 / 3 : ℝ) := by
      conv_lhs => arg 2; rw [← Real.rpow_one D]
      rw [mul_assoc, ← Real.rpow_add hDp]; norm_num
    rw [hid] at ht
    nlinarith
  exact ⟨hD, hM10, hMQ, hQK, hlogM, by simpa only [K, Q, Nat.cast_mul, pow_two] using hratio,
    honesave, hsmallsave, by simpa only [Q, Nat.cast_mul, pow_two] using hendsave⟩

#print axioms eventually_fourier_power_margins

end ReflectedLiouville
