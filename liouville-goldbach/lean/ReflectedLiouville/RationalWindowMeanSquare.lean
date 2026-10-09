import ReflectedLiouville.IntegratedVariance
import ReflectedLiouville.OriginAverage

set_option autoImplicit false
open scoped BigOperators

namespace ReflectedLiouville

/-- Rational quotient-window mean square with explicit variance, short-origin
    and endpoint-error terms. The phase a/q₀ stays fixed during the averages. -/
theorem rational_window_mean_square
    (h_KMT : KMTInput) (h_MRT : MRTRealTwistRepulsionInput) :
    ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∃ C X₀ : ℝ, 0 < C ∧ 10 ≤ X₀ ∧
      ∀ (N q₀ K h : ℕ) [NeZero N] [NeZero q₀] [NeZero K], h ≤ K → 10 * q₀ ≤ h →
        X₀ ≤ ((N * h : ℕ) : ℝ) →
        Real.exp ((Real.log ((N * K : ℕ) : ℝ)) ^ ν) ≤ (h : ℝ) / q₀ →
        ∀ a : ℤ,
          (∑ v ∈ Finset.range K, ∑ r : Fin N,
            ‖rationalQuotientWindow N q₀ (r.val + 1) v h a‖ ^ (2 : ℕ)) / ((N : ℝ) * K) ≤
          4 * C * (h : ℝ) ^ (2 : ℕ) / Real.rpow (Real.log ((h : ℝ) / q₀)) (1 / 1000) +
            18 * (h : ℝ) ^ (3 : ℕ) / K + 8 * (q₀ : ℝ) ^ (2 : ℕ) := by
  intro ν hν hν₁
  obtain ⟨C, X₀, hC, hX₀, henergy⟩ := initial_to_length_variance h_KMT h_MRT ν hν hν₁
  refine ⟨C, X₀, hC, hX₀, ?_⟩
  intro N q₀ K h instN instQ instK hhK hhQ hX hR a
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hQ : (0 : ℝ) < q₀ := by exact_mod_cast NeZero.pos q₀
  have hK : (0 : ℝ) < K := by exact_mod_cast NeZero.pos K
  have hHle : ((N * h : ℕ) : ℝ) ≤ ((N * K : ℕ) : ℝ) := by exact_mod_cast Nat.mul_le_mul_left N hhK
  have hHq : 10 * ((N * q₀ : ℕ) : ℝ) ≤ ((N * h : ℕ) : ℝ) := by
    have hnat : 10 * (N * q₀) ≤ N * h := by
      have h := Nat.mul_le_mul_left N hhQ
      nlinarith
    exact_mod_cast hnat
  have hratio : (((N * h : ℕ) : ℝ) / ((N * q₀ : ℕ) : ℝ)) = (h : ℝ) / q₀ := by
    push_cast
    field_simp
  have henergy' := henergy (N * q₀) ((N * K : ℕ) : ℝ) ((N * h : ℕ) : ℝ) hX hHle hHq
    (by rwa [hratio])
  rw [hratio] at henergy'
  have hbridge := rational_windows_discrete_to_integral N q₀ K h a
  have hscaled := mul_le_mul_of_nonneg_left henergy' (by positivity : 0 ≤ 2 * (q₀ : ℝ) / N)
  have hsum := add_le_add_right hscaled (8 * (N : ℝ) * K * (q₀ : ℝ) ^ (2 : ℕ))
  have hbound := hbridge.trans (by simpa only [add_comm] using hsum)
  have hdiv := div_le_div_of_nonneg_right hbound (by positivity : 0 ≤ (N : ℝ) * K)
  apply hdiv.trans_eq
  push_cast
  field_simp <;> ring

#print axioms rational_window_mean_square

end ReflectedLiouville
