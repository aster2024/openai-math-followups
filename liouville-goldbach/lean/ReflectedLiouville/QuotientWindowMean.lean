import ReflectedLiouville.RationalWindowMeanSquare
import ReflectedLiouville.QuotientPerturbation
import ReflectedLiouville.FiniteCauchy

set_option autoImplicit false
open scoped BigOperators

namespace ReflectedLiouville

lemma window_mean_from_square (N K : ℕ) [NeZero N] [NeZero K] (W : ℕ → Fin N → ℂ) :
    (∑ v ∈ Finset.range K, ∑ r : Fin N, ‖W v r‖) / ((N : ℝ) * K) ≤
      Real.sqrt ((∑ v ∈ Finset.range K, ∑ r : Fin N, ‖W v r‖ ^ (2 : ℕ)) / ((N : ℝ) * K)) := by
  let S := (Finset.range K) ×ˢ (Finset.univ : Finset (Fin N))
  have hS : 0 < S.card := by
    simp only [S, Finset.card_product, Finset.card_range, Finset.card_univ, Fintype.card_fin]
    exact Nat.mul_pos (NeZero.pos K) (NeZero.pos N)
  have h := finite_mean_norm_le_sqrt_mean_square S (fun vr => W vr.1 vr.2) hS
  simp only [S, Finset.sum_product, Finset.card_product, Finset.card_range, Finset.card_univ,
    Fintype.card_fin, Nat.cast_mul] at h
  simpa only [mul_comm (K : ℝ)] using h

theorem rational_window_mean_norm
    (h_KMT : KMTInput) (h_MRT : MRTRealTwistRepulsionInput) :
    ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∃ C X₀ : ℝ, 0 < C ∧ 10 ≤ X₀ ∧
      ∀ (N q₀ K h : ℕ) [NeZero N] [NeZero q₀] [NeZero K], h ≤ K → 10 * q₀ ≤ h →
        X₀ ≤ ((N * h : ℕ) : ℝ) → Real.exp ((Real.log ((N * K : ℕ) : ℝ)) ^ ν) ≤ (h : ℝ) / q₀ →
        ∀ a : ℤ,
          (∑ v ∈ Finset.range K, ∑ r : Fin N, ‖rationalQuotientWindow N q₀ (r.val + 1) v h a‖) / ((N : ℝ) * K) ≤
          Real.sqrt (4 * C * (h : ℝ) ^ (2 : ℕ) / Real.rpow (Real.log ((h : ℝ) / q₀)) (1 / 1000) +
            18 * (h : ℝ) ^ (3 : ℕ) / K + 8 * (q₀ : ℝ) ^ (2 : ℕ)) := by
  intro ν hν hν₁
  obtain ⟨C, X₀, hC, hX₀, hsq⟩ := rational_window_mean_square h_KMT h_MRT ν hν hν₁
  refine ⟨C, X₀, hC, hX₀, ?_⟩
  intro N q₀ K h instN instQ instK hhK hhQ hX hR a
  apply (window_mean_from_square N K (fun v r => rationalQuotientWindow N q₀ (r.val + 1) v h a)).trans
  exact Real.sqrt_le_sqrt (hsq N q₀ K h hhK hhQ hX hR a)

lemma quotient_window_norm_trivial (N r v h : ℕ) (θ : ℝ) :
    ‖quotientWindowFrequency N r v h θ‖ ≤ (h : ℝ) := by
  unfold quotientWindowFrequency
  calc
    _ ≤ ∑ m ∈ Finset.Icc (v + 1) (v + h), ‖liouville (N * m + r) * OAI.TwoPointCorrelations.additiveCharacter θ m‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _m ∈ Finset.Icc (v + 1) (v + h), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro m hm
      rw [norm_mul, OAI.TwoPointCorrelations.norm_additiveCharacter, mul_one]
      exact norm_liouville_le _
    _ = _ := by simp

#print axioms rational_window_mean_norm

end ReflectedLiouville
