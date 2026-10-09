import ReflectedLiouville.Indicators
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false
open Filter
open scoped BigOperators

namespace ReflectedLiouville

/-- This is a derived-lemma interface, not a published analytic hypothesis. -/
def LinearLogSaving : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, 3 ≤ N₀ ∧
    ∀ N : ℕ, N₀ ≤ N →
      |linearSum N| ≤ C * (N : ℝ) / Real.rpow (Real.log (N : ℝ)) c

lemma abs_sign_cast {e : ℤ} (he : IsSign e) : |(e : ℝ)| = 1 := by
  rcases he with rfl | rfl <;> norm_num

/-- A pointwise error transfer, including the actual missing endpoint 1/4. -/
lemma sign_pattern_error_bound (N : ℕ) (hN : 2 ≤ N) (e₁ e₂ : ℤ)
    (he₁ : IsSign e₁) (he₂ : IsSign e₂) :
    |(signPatternCount N e₁ e₂ : ℝ) - (N : ℝ) / 4| ≤
      (1 + 2 * |linearSum N| + |reflectedSum N|) / 4 := by
  rw [sign_pattern_count_identity N hN e₁ e₂ he₁ he₂]
  have he : |(e₁ : ℝ) + (e₂ : ℝ)| ≤ 2 := by
    exact (abs_add_le _ _).trans (by rw [abs_sign_cast he₁, abs_sign_cast he₂]; norm_num)
  have hprod : |(e₁ : ℝ) * (e₂ : ℝ)| = 1 := by
    rw [abs_mul, abs_sign_cast he₁, abs_sign_cast he₂, mul_one]
  have hlin : |((e₁ : ℝ) + (e₂ : ℝ)) * linearSum N| ≤ 2 * |linearSum N| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right he (abs_nonneg _)
  have hc : |(e₁ : ℝ) * (e₂ : ℝ) * reflectedSum N| = |reflectedSum N| := by
    rw [abs_mul, hprod, one_mul]
  have heq :
      ((N : ℝ) - 1 + ((e₁ : ℝ) + e₂) * linearSum N +
        (e₁ : ℝ) * e₂ * reflectedSum N) / 4 - (N : ℝ) / 4 =
      (-1 + ((e₁ : ℝ) + e₂) * linearSum N +
        (e₁ : ℝ) * e₂ * reflectedSum N) / 4 := by ring
  rw [heq, abs_div]
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 4)
  calc
    _ ≤ |-1 + ((e₁ : ℝ) + e₂) * linearSum N| +
        |(e₁ : ℝ) * e₂ * reflectedSum N| := abs_add_le _ _
    _ ≤ (|-1| + |((e₁ : ℝ) + e₂) * linearSum N|) + |reflectedSum N| := by
      rw [hc]
      exact add_le_add (abs_add_le _ _) le_rfl
    _ ≤ _ := by
      norm_num only [abs_neg, abs_one]
      linarith

lemma log_saving_error_antitone (N : ℕ) (hlog : 1 ≤ Real.log (N : ℝ))
    (c d C : ℝ) (hC : 0 ≤ C) (hcd : c ≤ d) :
    C * (N : ℝ) / Real.rpow (Real.log (N : ℝ)) d ≤
      C * (N : ℝ) / Real.rpow (Real.log (N : ℝ)) c := by
  apply div_le_div_of_nonneg_left (by positivity)
    (Real.rpow_pos_of_pos (by linarith) c)
  exact Real.rpow_le_rpow_of_exponent_le hlog hcd

lemma log_saving_error_eventually_ge_one (c : ℝ) :
    ∀ᶠ N : ℕ in atTop, 1 ≤ (N : ℝ) / Real.rpow (Real.log (N : ℝ)) c := by
  have h := (tendsto_exp_div_rpow_atTop c).comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [h.eventually (eventually_ge_atTop (1 : ℝ)), eventually_ge_atTop (1 : ℕ)]
    with N hN hpos
  change 1 ≤ Real.exp (Real.log (N : ℝ)) / Real.rpow (Real.log (N : ℝ)) c at hN
  rwa [Real.exp_log (by exact_mod_cast hpos : (0 : ℝ) < N)] at hN

/-- The full sign-count corollary follows from the two actual saving lemmas.
    Neither premise is represented as a published theorem. -/
theorem sign_patterns_of_two_savings (hc : ReflectedLogSaving) (hl : LinearLogSaving) :
    SignPatternLogSaving := by
  obtain ⟨c, hcpos, C, hCpos, N₀, hN₀, hcorr⟩ := hc
  obtain ⟨d, hdpos, D, hDpos, N₁, hN₁, hlinear⟩ := hl
  let e := min c d
  have hepos : 0 < e := lt_min hcpos hdpos
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp (log_saving_error_eventually_ge_one e)
  obtain ⟨N₃, hN₃⟩ := eventually_atTop.mp
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (1 : ℝ)))
  refine ⟨e, hepos, (1 + 2 * D + C) / 4, by positivity,
    max (max N₀ N₁) (max N₂ N₃), ?_, ?_⟩
  · exact hN₀.trans ((le_max_left _ _).trans (le_max_left _ _))
  · intro N hN e₁ e₂ he₁ he₂
    have h0 : N₀ ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
    have h1 : N₁ ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
    have h2 : N₂ ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
    have h3 : N₃ ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
    have hlog := hN₃ N h3
    have he1 := hN₂ N h2
    have hc' := (hcorr N h0).trans
      (log_saving_error_antitone N hlog e c C hCpos.le (min_le_left _ _))
    have hl' := (hlinear N h1).trans
      (log_saving_error_antitone N hlog e d D hDpos.le (min_le_right _ _))
    apply (sign_pattern_error_bound N (by omega) e₁ e₂ he₁ he₂).trans
    have hsaving : 0 ≤ (N : ℝ) / Real.rpow (Real.log (N : ℝ)) e := by positivity
    calc
      _ ≤ ((1 + 2 * D + C) * ((N : ℝ) / Real.rpow (Real.log (N : ℝ)) e)) / 4 := by
        have hcl : |reflectedSum N| ≤ C * ((N : ℝ) / Real.rpow (Real.log (N : ℝ)) e) := by
          simpa only [mul_div_assoc] using hc'
        have hll : |linearSum N| ≤ D * ((N : ℝ) / Real.rpow (Real.log (N : ℝ)) e) := by
          simpa only [mul_div_assoc] using hl'
        linarith
      _ = _ := by ring

#print axioms sign_patterns_of_two_savings

end ReflectedLiouville
