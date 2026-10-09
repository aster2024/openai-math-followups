import ReflectedLiouville.AnalyticTargets
import ReflectedLiouville.CharacterAlgebra
import ReflectedLiouville.PrimeTailTransfer
import Mathlib.Tactic

set_option autoImplicit false
open scoped BigOperators ComplexConjugate

namespace ReflectedLiouville

lemma real_character_conj {q : ℕ} (χ : DirichletCharacter ℂ q) (hχ : RealCharacter χ)
    (a : ZMod q) : conj (χ a) = χ a := by
  apply Complex.ext
  · simp
  · simp [hχ a]

lemma characterMean_real_eq {q : ℕ} (χ : DirichletCharacter ℂ q) (hχ : RealCharacter χ)
    (X : ℝ) :
    characterMean liouville χ X =
      ∑ n ∈ Finset.Icc 1 ⌊3 * X⌋₊, liouville n * χ (n : ZMod q) := by
  unfold characterMean
  apply Finset.sum_congr rfl
  intro n hn
  rw [real_character_conj χ hχ]

lemma kmtRealMainTerm_norm_real {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : RealCharacter χ) (X H : ℝ)
    (hX : 0 < X) (hH : 0 ≤ H) (a : (ZMod q)ˣ) :
    ‖kmtRealMainTerm liouville χ X H (a : ZMod q)‖ =
      H / ((Nat.totient q : ℝ) * (3 * X)) * ‖characterMean liouville χ X‖ := by
  have hφ : (0 : ℝ) < Nat.totient q := by
    exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  rw [kmtRealMainTerm, if_pos hχ, norm_mul, norm_mul, norm_div,
    χ.unit_norm_eq_one, Complex.norm_natCast, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (div_nonneg hH (by positivity))]
  congr 1
  field_simp

lemma kmtRealMainTerm_norm_nonreal {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hχ : ¬ RealCharacter χ) (X H : ℝ) (a : ZMod q) :
    ‖kmtRealMainTerm liouville χ X H a‖ = 0 := by
  simp only [kmtRealMainTerm, if_neg hχ, norm_zero]

/-- h_tail is a derived target supplied by the realmean module, not a published
    input. Nonreal main terms have been deleted by the faithful KMT input. -/
theorem kmt_main_term_pointwise_bound (h_MRT : MRTRealTwistRepulsionInput)
    (h_tail : RealCharacterPrimeTailBound) :
    ∃ C X₀ : ℝ, 0 < C ∧ 10 ≤ X₀ ∧ ∀ X H : ℝ, X₀ ≤ X → 0 ≤ H →
      ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ X →
        ∀ (χ : DirichletCharacter ℂ q) (a : (ZMod q)ˣ),
          ‖kmtRealMainTerm liouville χ X H (a : ZMod q)‖ ≤
            C * H / ((Nat.totient q : ℝ) * Real.rpow (Real.log X) (1 / 40)) := by
  obtain ⟨C, X₀, hC, hX₀, hmean⟩ := real_character_mean_of_prime_tail h_MRT h_tail
  refine ⟨C, max X₀ (Real.exp 1), hC, hX₀.trans (le_max_left _ _), ?_⟩
  intro X H hX hH q inst hqX χ a
  have hXX₀ : X₀ ≤ X := (le_max_left _ _).trans hX
  have hXp : 0 < X := by linarith
  have hφ : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hlog : 1 ≤ Real.log X := by
    have h := Real.log_le_log (Real.exp_pos 1) ((le_max_right _ _).trans hX)
    simpa only [Real.log_exp] using h
  have hPow : 0 < Real.rpow (Real.log X) (1 / 40) := Real.rpow_pos_of_pos (by linarith) _
  by_cases hreal : RealCharacter χ
  · rw [kmtRealMainTerm_norm_real χ hreal X H hXp hH a]
    have hlog3 : Real.log X ≤ Real.log (3 * X) := Real.log_le_log hXp (by linarith)
    have hpow : Real.rpow (Real.log X) (1 / 40) ≤ Real.rpow (Real.log (3 * X)) (1 / 40) :=
      Real.rpow_le_rpow (by linarith) hlog3 (by norm_num)
    have hmain : ‖characterMean liouville χ X‖ ≤ C * (3 * X) /
        Real.rpow (Real.log X) (1 / 40) := by
      have hm := hmean (3 * X) (by linarith) q (by linarith) χ hreal
      rw [← characterMean_real_eq χ hreal X] at hm
      apply hm.trans
      exact div_le_div_of_nonneg_left (by positivity) hPow hpow
    apply (mul_le_mul_of_nonneg_left hmain (by positivity : 0 ≤ H / ((q.totient : ℝ) * (3 * X)))).trans_eq
    field_simp
  · rw [kmtRealMainTerm_norm_nonreal χ hreal]
    exact div_nonneg (mul_nonneg hC.le hH) (mul_nonneg hφ.le hPow.le)

lemma constant_unit_square_bound {q : ℕ} [NeZero q] (v : (ZMod q)ˣ → ℂ)
    (C H t : ℝ) (hC : 0 ≤ C) (hH : 0 ≤ H) (ht : 0 < t)
    (hbound : ∀ a, ‖v a‖ ≤ C * H / ((q.totient : ℝ) * t)) :
    (∑ a : (ZMod q)ˣ, ‖v a‖ ^ 2) ≤ C ^ 2 * H ^ 2 / ((q.totient : ℝ) * t ^ 2) := by
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  calc
    _ ≤ ∑ _a : (ZMod q)ˣ, (C * H / ((q.totient : ℝ) * t)) ^ 2 := by
      apply Finset.sum_le_sum
      intro a ha
      exact pow_le_pow_left₀ (norm_nonneg _) (hbound a) 2
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, ZMod.card_units_eq_totient, nsmul_eq_mul]
      field_simp

lemma log_rpow_square (X : ℝ) (hlog : 0 ≤ Real.log X) :
    (Real.rpow (Real.log X) (1 / 40)) ^ (2 : ℕ) = Real.rpow (Real.log X) (1 / 20) := by
  simp only [Real.rpow_eq_pow]
  rw [← Real.rpow_mul_natCast hlog]
  congr 1
  norm_num

set_option maxHeartbeats 1000000 in
/-- Summed unit-class energy with the true totient factor. h_tail is the derived
    target supplied by the realmean module, not a published input. -/
theorem kmt_main_term_square_sum (h_MRT : MRTRealTwistRepulsionInput)
    (h_tail : RealCharacterPrimeTailBound) :
    ∃ C X₀ : ℝ, 0 < C ∧ 10 ≤ X₀ ∧ ∀ X H : ℝ, X₀ ≤ X → 0 ≤ H →
      ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ X → ∀ χ : DirichletCharacter ℂ q,
        (∑ a : (ZMod q)ˣ, ‖kmtRealMainTerm liouville χ X H (a : ZMod q)‖ ^ 2) ≤
          C ^ 2 * H ^ 2 / ((q.totient : ℝ) * Real.rpow (Real.log X) (1 / 20)) := by
  obtain ⟨C, X₀, hC, hX₀, hpoint⟩ := kmt_main_term_pointwise_bound h_MRT h_tail
  refine ⟨C, max X₀ (Real.exp 1), hC, hX₀.trans (le_max_left _ _), ?_⟩
  intro X H hX hH q inst hqX χ
  have hlog : 1 ≤ Real.log X := by
    have h := Real.log_le_log (Real.exp_pos 1) ((le_max_right _ _).trans hX)
    simpa only [Real.log_exp] using h
  have hb := constant_unit_square_bound (q := q)
    (fun a : (ZMod q)ˣ => kmtRealMainTerm liouville χ X H (a : ZMod q)) C H
    (Real.rpow (Real.log X) (1 / 40)) hC.le hH
    (Real.rpow_pos_of_pos (by linarith) _) (hpoint X H ((le_max_left _ _).trans hX) hH q hqX χ)
  rwa [log_rpow_square X (by linarith)] at hb

noncomputable def kmtMainTermEnergy {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (X H : ℝ) : ℝ :=
  ∫ _x in X..2 * X, ∑ a : (ZMod q)ˣ, ‖kmtRealMainTerm liouville χ X H (a : ZMod q)‖ ^ 2

lemma kmtMainTermEnergy_eq {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (X H : ℝ) :
    kmtMainTermEnergy χ X H = X *
      (∑ a : (ZMod q)ˣ, ‖kmtRealMainTerm liouville χ X H (a : ZMod q)‖ ^ 2) := by
  simp only [kmtMainTermEnergy, intervalIntegral.integral_const, smul_eq_mul]
  ring

#print axioms kmt_main_term_pointwise_bound
#print axioms kmt_main_term_square_sum

end ReflectedLiouville
