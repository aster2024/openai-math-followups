import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace ReflectedLiouville

/-- The exact q₀≤Q₀ and |β|≤1/(q₀Q₀) approximation used by the paper. -/
theorem exists_rational_frequency (θ : ℝ) (Q₀ : ℕ) (hQ : 0 < Q₀) :
    ∃ (a : ℤ) (q₀ : ℕ) (β : ℝ), 0 < q₀ ∧ q₀ ≤ Q₀ ∧
      θ = (a : ℝ) / q₀ + β ∧ |β| ≤ 1 / ((q₀ : ℝ) * Q₀) := by
  obtain ⟨q₀, hq, hqQ, hround⟩ := Real.exists_nat_abs_mul_sub_round_le θ hQ
  let a : ℤ := round ((q₀ : ℝ) * θ)
  let β := θ - (a : ℝ) / q₀
  have hqp : (0 : ℝ) < q₀ := by exact_mod_cast hq
  have hQp : (0 : ℝ) < Q₀ := by exact_mod_cast hQ
  refine ⟨a, q₀, β, hq, hqQ, by dsimp [β]; ring, ?_⟩
  have hid : β = ((q₀ : ℝ) * θ - a) / q₀ := by dsimp [β]; field_simp <;> ring
  rw [hid, abs_div, abs_of_pos hqp]
  calc
    _ ≤ (1 / ((Q₀ : ℝ) + 1)) / q₀ := div_le_div_of_nonneg_right hround hqp.le
    _ ≤ (1 / (Q₀ : ℝ)) / q₀ := div_le_div_of_nonneg_right
      (div_le_div_of_nonneg_left zero_le_one hQp (by linarith)) hqp.le
    _ = _ := by ring

#print axioms exists_rational_frequency

end ReflectedLiouville
