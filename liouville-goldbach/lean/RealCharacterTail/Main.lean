import RealCharacterTail.UniformApproximation
import RealCharacterTail.Parameters
import RealCharacterTail.FiniteTail

set_option autoImplicit false
open scoped BigOperators Topology
open Set Filter

namespace RealCharacterTail

/-- The exact target from the main project, proved without additional inputs.
    The proof in fact controls the complex sum for every nonprincipal character. -/
theorem real_character_prime_tail :
  ∃ C X₀ : ℝ, 0 < C ∧ 100 ≤ X₀ ∧ ∀ X : ℝ, X₀ ≤ X →
    ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ X →
      ∀ χ : DirichletCharacter ℂ q, (∀ a : ZMod q, (χ a).im = 0) → χ ≠ 1 →
        |∑ p ∈ (OAI.TwoPointCorrelations.primesUpTo ⌊X⌋₊).filter
          (fun p : ℕ => (Real.log X) ^ (64 : ℕ) < (p : ℝ)), (χ (p : ZMod q)).re / p| ≤ C := by
  let E : ℝ := 1 + primePowerErrorConstant + 2000000 * parameterConstant
  have hE : 0 < E := by
    have hp := primePowerErrorConstant_nonneg
    have hk := parameterConstant_pos
    dsimp [E]
    positivity
  obtain ⟨a, ha⟩ := eventually_atTop.mp eventually_cutoff_range
  refine ⟨2 * E, max a 100, by positivity, le_max_right _ _, ?_⟩
  intro X hX q _ hqX χ _hreal hχ
  have hXa : a ≤ X := (le_max_left a 100).trans hX
  obtain ⟨hX100, hlog, hY2, hYX⟩ := ha X hXa
  let Y := (Real.log X) ^ (64 : ℕ)
  have hXp : 0 < X := by linarith
  have hT : 1 ≤ X ^ 4 := one_le_pow₀ (by linarith : 1 ≤ X)
  obtain ⟨z, hz⟩ := prime_sum_approximation χ hχ
  have hpoint (x : ℝ) (hyx : Y ≤ x) (hxX : x ≤ X) :
      ‖primeReciprocalSum χ x - z‖ ≤ E := by
    have hx2 : 2 ≤ x := hY2.trans hyx
    have hx0 : 0 ≤ x := by linarith
    have he := parameter_error_bound hX100 hlog hqX hx0 hyx hxX
    have hb := hz x (X ^ 4) hx2 hT
    have hm := mul_le_mul_of_nonneg_left he (by norm_num : (0 : ℝ) ≤ 1000000)
    have hm' : 1000000 * (Real.log (20 * (q : ℝ) * (X ^ 4 + 2)) + 1) *
        (x ^ (-1 / 16 : ℝ) + x ^ 2 / X ^ 4) ≤ 2000000 * parameterConstant := by
      nlinarith only [hm]
    dsimp [E]
    linarith
  have hPX := hpoint X hYX le_rfl
  have hPY := hpoint Y le_rfl hYX
  apply (real_prime_tail_le_norm χ (by linarith) hYX).trans
  have he : primeReciprocalSum χ X - primeReciprocalSum χ Y =
      (primeReciprocalSum χ X - z) - (primeReciprocalSum χ Y - z) := by ring
  rw [he]
  exact (norm_sub_le _ _).trans (by linarith)

end RealCharacterTail

#print axioms RealCharacterTail.real_character_prime_tail
