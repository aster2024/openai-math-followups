import ReflectedLiouville.KMTMargins
import Mathlib.Tactic

set_option autoImplicit false

namespace ReflectedLiouville

/-- The exact buffer inequality required by the reviewed KMT input. -/
lemma kmt_q_buffer_of_growth (q H Q ρ : ℝ) (hq : 0 < q) (hH : 0 < H)
    (hR : 1 ≤ H / q) (hρ : 0 ≤ ρ) (hbuffer : q * (H / q) ^ (ρ / 50) ≤ Q) :
    q * (H / Q) ^ (ρ / 100) ≤ Q := by
  have hpow : 1 ≤ (H / q) ^ (ρ / 50) := Real.one_le_rpow hR (by positivity)
  have hqQ : q ≤ Q := (le_mul_of_one_le_right hq.le hpow).trans hbuffer
  have hQ : 0 < Q := hq.trans_le hqQ
  have hRR : H / Q ≤ H / q := div_le_div_of_nonneg_left hH.le hq hqQ
  calc
    _ ≤ q * (H / q) ^ (ρ / 100) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) hRR (by positivity)) hq.le
    _ ≤ q * (H / q) ^ (ρ / 50) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hR (by linarith)) hq.le
    _ ≤ _ := hbuffer

lemma kmt_log_cap_of_buffer (X H Q : ℝ) (hH : 0 < H) (hQ : 0 < Q)
    (hcap : H * Real.exp (-(Real.log X) ^ (2 / 5 : ℝ)) ≤ Q) :
    Real.log (H / Q) ≤ (Real.log X) ^ (2 / 5 : ℝ) := by
  have hm := mul_le_mul_of_nonneg_right hcap (Real.exp_pos ((Real.log X) ^ (2 / 5 : ℝ))).le
  have hexp : Real.exp (-(Real.log X) ^ (2 / 5 : ℝ)) *
      Real.exp ((Real.log X) ^ (2 / 5 : ℝ)) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  rw [mul_assoc, hexp, mul_one] at hm
  have hquot : H / Q ≤ Real.exp ((Real.log X) ^ (2 / 5 : ℝ)) :=
    (div_le_iff₀ hQ).mpr (by simpa only [mul_comm] using hm)
  have hlog := Real.log_le_log (div_pos hH hQ) hquot
  simpa only [Real.log_exp] using hlog

/-- The manuscript's integer ceil upper bound; X and H are real as published. -/
noncomputable def kmtBufferedQ (X H ρ : ℝ) (q : ℕ) : ℕ :=
  ⌈max ((q : ℝ) * (H / q) ^ (ρ / 50))
    (H * Real.exp (-(Real.log X) ^ (2 / 5 : ℝ)))⌉₊

lemma kmtBufferedQ_lower (X H ρ : ℝ) (q : ℕ) :
    (q : ℝ) * (H / q) ^ (ρ / 50) ≤ kmtBufferedQ X H ρ q ∧
      H * Real.exp (-(Real.log X) ^ (2 / 5 : ℝ)) ≤ kmtBufferedQ X H ρ q := by
  have h := Nat.le_ceil (max ((q : ℝ) * (H / q) ^ (ρ / 50))
    (H * Real.exp (-(Real.log X) ^ (2 / 5 : ℝ))))
  exact ⟨(le_max_left _ _).trans h, (le_max_right _ _).trans h⟩

/-- Both new R1 premises are proved for the actual buffered modulus. -/
lemma kmtBufferedQ_reviewed_premises (X H ρ : ℝ) (q : ℕ) [NeZero q]
    (hH : 0 < H) (hR : 1 ≤ H / q) (hρ : 0 ≤ ρ) :
    (q : ℝ) * (H / kmtBufferedQ X H ρ q) ^ (ρ / 100) ≤ kmtBufferedQ X H ρ q ∧
      Real.log (H / kmtBufferedQ X H ρ q) ≤ (Real.log X) ^ (2 / 5 : ℝ) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hlow := kmtBufferedQ_lower X H ρ q
  have hqQ : (q : ℝ) ≤ kmtBufferedQ X H ρ q :=
    (le_mul_of_one_le_right hq.le (Real.one_le_rpow hR (by positivity))).trans hlow.1
  have hQ : (0 : ℝ) < kmtBufferedQ X H ρ q := hq.trans_le hqQ
  exact ⟨kmt_q_buffer_of_growth _ _ _ _ hq hH hR hρ hlow.1,
    kmt_log_cap_of_buffer _ _ _ hH hQ hlow.2⟩

#print axioms kmtBufferedQ_reviewed_premises

end ReflectedLiouville
