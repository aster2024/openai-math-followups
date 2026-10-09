import ReflectedLiouville.KMTBuffer
import Mathlib.Tactic

set_option autoImplicit false

namespace ReflectedLiouville

lemma buffered_growth_as_exponential (q H κ : ℝ) (hq : 0 < q) (hH : 0 < H) :
    q * (H / q) ^ κ = H * Real.exp ((κ - 1) * Real.log (H / q)) := by
  rw [Real.rpow_def_of_pos (div_pos hH hq),
    show (κ - 1) * Real.log (H / q) = Real.log (H / q) * κ - Real.log (H / q) by ring,
    Real.exp_sub, Real.exp_log (div_pos hH hq)]
  field_simp

lemma ceil_max_le_twice (a b : ℝ) (ha : 1 ≤ a) :
    (⌈max a b⌉₊ : ℝ) ≤ 2 * max a b := by
  have hmax : 1 ≤ max a b := ha.trans (le_max_left _ _)
  have hceil := Nat.ceil_lt_add_one (by linarith : 0 ≤ max a b)
  linarith

lemma kmtBufferedQ_exp_upper (X H ρ : ℝ) (q : ℕ) [NeZero q]
    (hX : 1 ≤ X) (hH : 0 < H) (hR : 1 ≤ H / q) (hρ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1) :
    (kmtBufferedQ X H ρ q : ℝ) ≤ 2 * H * Real.exp
      (-(49 / 50 : ℝ) * min (Real.log (H / q)) ((Real.log X) ^ (2 / 5 : ℝ))) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hq₁ : (1 : ℝ) ≤ q := by exact_mod_cast (NeZero.pos q)
  have hS : 0 ≤ Real.log (H / q) := Real.log_nonneg hR
  have hA : 1 ≤ (q : ℝ) * (H / q) ^ (ρ / 50) :=
    hq₁.trans (le_mul_of_one_le_right hq.le (Real.one_le_rpow hR (by positivity)))
  have hmax : max ((q : ℝ) * (H / q) ^ (ρ / 50))
      (H * Real.exp (-(Real.log X) ^ (2 / 5 : ℝ))) ≤
      H * Real.exp (-(49 / 50 : ℝ) * min (Real.log (H / q)) ((Real.log X) ^ (2 / 5 : ℝ))) := by
    apply max_le
    · rw [buffered_growth_as_exponential _ _ _ hq hH]
      apply mul_le_mul_of_nonneg_left _ hH.le
      apply Real.exp_le_exp.mpr
      have hκ : ρ / 50 - 1 ≤ -(49 / 50 : ℝ) := by linarith
      have hfirst := mul_le_mul_of_nonneg_right hκ hS
      have hmin := min_le_left (Real.log (H / q)) ((Real.log X) ^ (2 / 5 : ℝ))
      linarith
    · apply mul_le_mul_of_nonneg_left _ hH.le
      apply Real.exp_le_exp.mpr
      have hB : 0 ≤ (Real.log X) ^ (2 / 5 : ℝ) := Real.rpow_nonneg (Real.log_nonneg hX) _
      have hmin := min_le_right (Real.log (H / q)) ((Real.log X) ^ (2 / 5 : ℝ))
      linarith
  have hceil := ceil_max_le_twice ((q : ℝ) * (H / q) ^ (ρ / 50))
    (H * Real.exp (-(Real.log X) ^ (2 / 5 : ℝ))) hA
  change (kmtBufferedQ X H ρ q : ℝ) ≤ 2 * max ((q : ℝ) * (H / q) ^ (ρ / 50))
    (H * Real.exp (-(Real.log X) ^ (2 / 5 : ℝ))) at hceil
  apply hceil.trans
  convert mul_le_mul_of_nonneg_left hmax (by norm_num : (0 : ℝ) ≤ 2) using 1 <;> ring

lemma kmtBufferedQ_log_lower (X H ρ : ℝ) (q : ℕ) [NeZero q]
    (hX : 1 ≤ X) (hH : 0 < H) (hR : 1 ≤ H / q) (hρ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1) :
    (49 / 50 : ℝ) * min (Real.log (H / q)) ((Real.log X) ^ (2 / 5 : ℝ)) - Real.log 2 ≤
      Real.log (H / kmtBufferedQ X H ρ q) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hlow := kmtBufferedQ_lower X H ρ q
  have hqQ : (q : ℝ) ≤ kmtBufferedQ X H ρ q :=
    (le_mul_of_one_le_right hq.le (Real.one_le_rpow hR (by positivity))).trans hlow.1
  have hQ : (0 : ℝ) < kmtBufferedQ X H ρ q := hq.trans_le hqQ
  have hu := kmtBufferedQ_exp_upper X H ρ q hX hH hR hρ hρ₁
  have hlog := Real.log_le_log hQ hu
  rw [Real.log_mul (by positivity : (2 * H : ℝ) ≠ 0) (Real.exp_ne_zero _),
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hH.ne', Real.log_exp] at hlog
  rw [Real.log_div hH.ne' hQ.ne']
  linarith

#print axioms kmtBufferedQ_log_lower

end ReflectedLiouville
