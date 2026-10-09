import ReflectedLiouville.KMTLogGeometry
import Mathlib.Tactic

set_option autoImplicit false

namespace ReflectedLiouville

lemma kmtBufferedQ_log_half (X H ρ : ℝ) (q : ℕ) [NeZero q]
    (hX : 1 ≤ X) (hH : 0 < H) (hR : 1 ≤ H / q) (hρ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1)
    (hmin : 3 * Real.log 2 ≤ min (Real.log (H / q)) ((Real.log X) ^ (2 / 5 : ℝ))) :
    min (Real.log (H / q)) ((Real.log X) ^ (2 / 5 : ℝ)) / 2 ≤
      Real.log (H / kmtBufferedQ X H ρ q) := by
  have hlog := kmtBufferedQ_log_lower X H ρ q hX hH hR hρ hρ₁
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  linarith

lemma kmtBufferedQ_le_length_tenth (X H ρ : ℝ) (q : ℕ) [NeZero q]
    (hX : 1 ≤ X) (hH : 0 < H) (hR : 1 ≤ H / q) (hρ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1)
    (hmin : 30 ≤ min (Real.log (H / q)) ((Real.log X) ^ (2 / 5 : ℝ))) :
    (kmtBufferedQ X H ρ q : ℝ) ≤ H / 10 := by
  have hlog20 : Real.log 20 ≤ 19 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 20)
    norm_num at h
    simpa only [one_div] using h
  have hexp : Real.exp (-(49 / 50 : ℝ) * min (Real.log (H / q)) ((Real.log X) ^ (2 / 5 : ℝ))) ≤ 1 / 20 := by
    have h := Real.exp_le_exp.mpr (by linarith :
      -(49 / 50 : ℝ) * min (Real.log (H / q)) ((Real.log X) ^ (2 / 5 : ℝ)) ≤ -Real.log 20)
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 20)] at h
    simpa only [one_div] using h
  calc
    _ ≤ 2 * H * Real.exp (-(49 / 50 : ℝ) * min (Real.log (H / q)) ((Real.log X) ^ (2 / 5 : ℝ))) :=
      kmtBufferedQ_exp_upper X H ρ q hX hH hR hρ hρ₁
    _ ≤ 2 * H * (1 / 20) := mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = _ := by ring

lemma kmtBufferedQ_ge_modulus (X H ρ : ℝ) (q : ℕ) [NeZero q]
    (hR : 1 ≤ H / q) (hρ : 0 ≤ ρ) : (q : ℝ) ≤ kmtBufferedQ X H ρ q := by
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  exact (le_mul_of_one_le_right hq (Real.one_le_rpow hR (by positivity))).trans
    (kmtBufferedQ_lower X H ρ q).1

#print axioms kmtBufferedQ_le_length_tenth

end ReflectedLiouville
