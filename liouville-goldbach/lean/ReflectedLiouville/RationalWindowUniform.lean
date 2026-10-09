import ReflectedLiouville.WindowPerturbationMean

set_option autoImplicit false
open scoped BigOperators

namespace ReflectedLiouville

lemma log_saving_comparison (L U : ℝ) (hL : 0 < L) (hU : L / 8 ≤ U) :
    1 / Real.rpow U (1 / 1000) ≤ 8 * Real.rpow L (-1 / 1000) := by
  have hLp : 0 < L / 8 := by positivity
  have hUp : 0 < U := hLp.trans_le hU
  have h := Real.rpow_le_rpow_of_nonpos hLp hU (by norm_num : (-1 / 1000 : ℝ) ≤ 0)
  have hf : (1 / 8 : ℝ) ^ (-1 / 1000 : ℝ) ≤ 8 := by
    have hc := Real.rpow_le_rpow_of_exponent_ge (by norm_num : (0 : ℝ) < 1 / 8)
      (by norm_num : (1 / 8 : ℝ) ≤ 1) (by norm_num : (-1 : ℝ) ≤ -1 / 1000)
    simpa only [Real.rpow_neg_one, inv_div, inv_one, mul_one, div_one] using hc
  have hsplit : (L / 8) ^ (-1 / 1000 : ℝ) =
      (1 / 8 : ℝ) ^ (-1 / 1000 : ℝ) * L ^ (-1 / 1000 : ℝ) := by
    rw [show L / 8 = (1 / 8 : ℝ) * L by ring, Real.mul_rpow (by norm_num) hL.le]
  rw [hsplit] at h
  have hfin := h.trans (mul_le_mul_of_nonneg_right hf (Real.rpow_nonneg hL.le _))
  simpa only [Real.rpow_eq_pow, neg_div, Real.rpow_neg hUp.le, one_div] using hfin

/-- Uniform normalization of the rational window's three exact error terms. -/
theorem rational_window_uniform_mean
    (h_KMT : KMTInput) (h_MRT : MRTRealTwistRepulsionInput) :
    ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∃ B X₀ : ℝ, 0 < B ∧ 10 ≤ X₀ ∧
      ∀ (N q K h m : ℕ) [NeZero N] [NeZero q] [NeZero K] (L : ℝ),
        0 < L → m ≤ h → h ≤ K → 10 * q ≤ m → X₀ ≤ ((N * m : ℕ) : ℝ) →
        Real.exp ((Real.log ((N * K : ℕ) : ℝ)) ^ ν) ≤ (m : ℝ) / q →
        L / 8 ≤ Real.log ((m : ℝ) / q) →
        (h : ℝ) / K ≤ Real.rpow L (-1 / 1000) →
        (q : ℝ) ^ (2 : ℕ) ≤ (m : ℝ) ^ (2 : ℕ) * Real.rpow L (-1 / 1000) →
        ∀ a : ℤ, ∀ t : ℕ, m ≤ t → t ≤ h →
          quotientWindowMean N K t ((a : ℝ) / q) ≤
            B * t * Real.rpow L (-1 / 2000) := by
  intro ν hν hν₁
  obtain ⟨C, X₀, hC, hX₀, hmean⟩ := rational_window_mean_norm h_KMT h_MRT ν hν hν₁
  let B := Real.sqrt (32 * C + 26)
  have hB : 0 < B := by dsimp [B]; exact Real.sqrt_pos.mpr (by linarith)
  refine ⟨B, X₀, hB, hX₀, ?_⟩
  intro N q K h m instN instQ instK L hL hmh hhK hmQ hX hR hlog hhsmall hqsmall a t hmt hth
  have htr : (m : ℝ) ≤ t := by exact_mod_cast hmt
  have hthr : (t : ℝ) ≤ h := by exact_mod_cast hth
  have htK : t ≤ K := hth.trans hhK
  have htQ : 10 * q ≤ t := hmQ.trans hmt
  have hXt : X₀ ≤ ((N * t : ℕ) : ℝ) := hX.trans (by exact_mod_cast Nat.mul_le_mul_left N hmt)
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hK : (0 : ℝ) < K := by exact_mod_cast NeZero.pos K
  have hRt : Real.exp ((Real.log ((N * K : ℕ) : ℝ)) ^ ν) ≤ (t : ℝ) / q :=
    hR.trans (div_le_div_of_nonneg_right htr hq.le)
  have hml : 0 < (m : ℝ) / q := by
    have hmpos : (0 : ℝ) < m := by have := NeZero.pos q; exact_mod_cast (show 0 < m by omega)
    positivity
  have hlogt : L / 8 ≤ Real.log ((t : ℝ) / q) := hlog.trans
    (Real.log_le_log hml (div_le_div_of_nonneg_right htr hq.le))
  have hcomp := log_saving_comparison L (Real.log ((t : ℝ) / q)) hL hlogt
  have hs : 0 ≤ Real.rpow L (-1 / 1000) := Real.rpow_nonneg hL.le _
  have ht : (0 : ℝ) ≤ t := by positivity
  have hfirst := mul_le_mul_of_nonneg_left hcomp (by positivity : 0 ≤ 4 * C * (t : ℝ) ^ (2 : ℕ))
  have hmid := mul_le_mul_of_nonneg_left
    ((div_le_div_of_nonneg_right hthr hK.le).trans hhsmall)
    (by positivity : 0 ≤ 18 * (t : ℝ) ^ (2 : ℕ))
  have hlast := hqsmall.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) htr 2) hs)
  have hsum : 4 * C * (t : ℝ) ^ (2 : ℕ) / Real.rpow (Real.log ((t : ℝ) / q)) (1 / 1000) +
      18 * (t : ℝ) ^ (3 : ℕ) / K + 8 * (q : ℝ) ^ (2 : ℕ) ≤
      (32 * C + 26) * (t : ℝ) ^ (2 : ℕ) * Real.rpow L (-1 / 1000) := by
    have hfirst' : 4 * C * (t : ℝ) ^ (2 : ℕ) / Real.rpow (Real.log ((t : ℝ) / q)) (1 / 1000) ≤
        32 * C * (t : ℝ) ^ (2 : ℕ) * Real.rpow L (-1 / 1000) := by convert hfirst using 1 <;> ring
    have hmid' : 18 * (t : ℝ) ^ (3 : ℕ) / K ≤ 18 * (t : ℝ) ^ (2 : ℕ) * Real.rpow L (-1 / 1000) := by
      convert hmid using 1 <;> ring
    linarith
  have h := (hmean N q K t htK htQ hXt hRt a).trans (Real.sqrt_le_sqrt hsum)
  change quotientWindowMean N K t ((a : ℝ) / q) ≤ _ at h
  have hsqrt : Real.sqrt ((32 * C + 26) * (t : ℝ) ^ (2 : ℕ) * Real.rpow L (-1 / 1000)) =
      B * t * Real.rpow L (-1 / 2000) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by linarith), Real.sqrt_sq ht]
    have hsave : Real.sqrt (Real.rpow L (-1 / 1000)) = Real.rpow L (-1 / 2000) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_eq_pow, ← Real.rpow_mul hL.le]
      congr 1
      norm_num
    rw [hsave]
  rwa [hsqrt] at h

#print axioms rational_window_uniform_mean

end ReflectedLiouville
