import RealCharacterTail.Approximation
import RealCharacterTail.Desmoothing

set_option autoImplicit false
open scoped Topology
open Set Filter MeasureTheory Complex Erdos970

namespace RealCharacterTail

theorem smoothed_uniform_bound {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (H : ℂ → ℂ)
    (hHd : DifferentiableOn ℂ H {s | (7 / 8 : ℝ) < s.re})
    (hExp : ∀ s : ℂ, (7 / 8 : ℝ) < s.re → Complex.exp (H s) = χ.LFunction s)
    (hEuler : ∀ s : ℂ, 1 < s.re → H s = LSeries (logCoeff χ) s)
    {x T : ℝ} (hx : 2 ≤ x) (hT : 1 ≤ T) :
    ‖smoothedReciprocalSum χ x - H 1‖ ≤
      1000000 * (Real.log (20 * (q : ℝ) * (T + 2)) + 1) *
        (x ^ (-1 / 16 : ℝ) + x ^ 2 / T) := by
  let B := Real.log (20 * (q : ℝ) * (T + 2)) + 1
  let r := x ^ (-1 / 16 : ℝ)
  let u := x ^ 2 / T
  have hxp : 0 < x := by linarith
  have hTp : 0 < T := by linarith
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hB : 1 ≤ B := by
    have hl : 0 ≤ Real.log (20 * (q : ℝ) * (T + 2)) := by
      apply Real.log_nonneg
      nlinarith [mul_le_mul_of_nonneg_right hq1 (by linarith : 0 ≤ T + 2)]
    dsimp [B]; linarith
  have hr : 0 ≤ r := Real.rpow_nonneg hxp.le _
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hH1 : ‖H 1‖ ≤ 200 * B := by
    simpa only [Complex.ofReal_one, Complex.ofReal_zero, zero_mul, add_zero] using
      norm_log_height_bound χ hχ H hHd hExp hEuler (σ := 1) (t := 0) (T := T)
        (by norm_num) (by norm_num) (by simpa using hTp.le)
  have hInv : 1 / x ≤ r := by
    have he := Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ x)
      (by norm_num : (-1 : ℝ) ≤ -1 / 16)
    simpa only [Real.rpow_neg_one, one_div] using he
  have hHterm : ‖H 1‖ / x ≤ 200 * B * r := by
    calc
      _ ≤ (200 * B) / x := div_le_div_of_nonneg_right hH1 hxp.le
      _ = (200 * B) * (1 / x) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hInv (by linarith)
  have hT2 : T ≤ T ^ 2 := by nlinarith
  have hU2 : x ^ 2 / T ^ 2 ≤ u := div_le_div_of_nonneg_left (sq_nonneg x) hTp hT2
  have htail : 2 * (3 / 2 + ‖H 1‖) * x ^ 2 / T ≤ 404 * B * u := by
    have hc : 2 * (3 / 2 + ‖H 1‖) ≤ 404 * B := by linarith
    calc
      _ = (2 * (3 / 2 + ‖H 1‖)) * u := by dsimp [u]; ring
      _ ≤ (404 * B) * u := mul_le_mul_of_nonneg_right hc hu
      _ = _ := by ring
  have ha := smoothed_approximation_bound χ hχ H hHd hExp hEuler hx hT
  calc
    _ ≤ ‖H 1‖ / x + 500000 * B * (r + x ^ 2 / T ^ 2) +
        2 * (3 / 2 + ‖H 1‖) * x ^ 2 / T := ha
    _ ≤ 200 * B * r + 500000 * B * (r + u) + 404 * B * u := by
      exact add_le_add (add_le_add hHterm
        (mul_le_mul_of_nonneg_left (add_le_add le_rfl hU2) (by linarith))) htail
    _ ≤ 1000000 * B * (r + u) := by
      nlinarith [mul_nonneg (by linarith : 0 ≤ B) hr, mul_nonneg (by linarith : 0 ≤ B) hu]

noncomputable def primePowerErrorConstant : ℝ :=
  OAI.SiegelZeros.W55.higherPrimePowerConstant / Real.log 2

lemma primePowerErrorConstant_nonneg : 0 ≤ primePowerErrorConstant :=
  div_nonneg OAI.SiegelZeros.W55.higherPrimePowerConstant_nonneg
    (Real.log_nonneg (by norm_num))

/-- A hypothesis-free analytic approximation, uniform in the modulus and character. -/
theorem prime_sum_approximation {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∃ z : ℂ, ∀ x T : ℝ, 2 ≤ x → 1 ≤ T →
      ‖primeReciprocalSum χ x - z‖ ≤ 1 + primePowerErrorConstant +
        1000000 * (Real.log (20 * (q : ℝ) * (T + 2)) + 1) *
          (x ^ (-1 / 16 : ℝ) + x ^ 2 / T) := by
  obtain ⟨H, hHd, hExp, hEuler⟩ := exists_normalized_log χ hχ
  refine ⟨H 1, ?_⟩
  intro x T hx hT
  have hp := prime_power_error_le χ x
  rw [norm_sub_rev] at hp
  have hd := desmoothing_error_le_one χ (by linarith : 0 < x)
  have ha := smoothed_uniform_bound χ hχ H hHd hExp hEuler hx hT
  have he : primeReciprocalSum χ x - H 1 =
      (primeReciprocalSum χ x - reciprocalMangoldtSum χ x) +
      (reciprocalMangoldtSum χ x - smoothedReciprocalSum χ x) +
      (smoothedReciprocalSum χ x - H 1) := by ring
  rw [he]
  calc
    _ ≤ (‖primeReciprocalSum χ x - reciprocalMangoldtSum χ x‖ +
          ‖reciprocalMangoldtSum χ x - smoothedReciprocalSum χ x‖) +
        ‖smoothedReciprocalSum χ x - H 1‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ primePowerErrorConstant + 1 +
        1000000 * (Real.log (20 * (q : ℝ) * (T + 2)) + 1) *
          (x ^ (-1 / 16 : ℝ) + x ^ 2 / T) := add_le_add (add_le_add hp hd) ha
    _ = _ := by ring

#print axioms smoothed_uniform_bound
#print axioms prime_sum_approximation

end RealCharacterTail
