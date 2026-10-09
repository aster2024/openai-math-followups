import RealCharacterTail.Smoothing
import OAI.NumberTheory.SiegelZeros.Characters.PrimePowerTail
import OAI.NumberTheory.TwoPoint.PretentiousDistance

set_option autoImplicit false
open scoped BigOperators Topology
open Set Filter MeasureTheory
open OAI.TwoPointCorrelations

namespace RealCharacterTail

noncomputable def reciprocalMangoldtSum {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, reciprocalCoeff χ n

noncomputable def primeReciprocalSum {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ℝ) : ℂ :=
  ∑ p ∈ primesUpTo ⌊x⌋₊, χ (p : ZMod q) / (p : ℂ)

/-- Removing the triangular weight has a uniform cost at most one. -/
theorem desmoothing_error_le_one {q : ℕ} (χ : DirichletCharacter ℂ q)
    {x : ℝ} (hx : 0 < x) :
    ‖reciprocalMangoldtSum χ x - smoothedReciprocalSum χ x‖ ≤ 1 := by
  have heq : reciprocalMangoldtSum χ x - smoothedReciprocalSum χ x =
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, logCoeff χ n / (x : ℂ) := by
    rw [reciprocalMangoldtSum, smoothedReciprocalSum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    have hn0 : (n : ℂ) ≠ 0 := by
      exact_mod_cast (show n ≠ 0 by have := (Finset.mem_Icc.mp hn).1; omega)
    simp only [reciprocalCoeff]
    push_cast
    field_simp
    ring
  rw [heq]
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ‖logCoeff χ n / (x : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.Icc 1 ⌊x⌋₊, (1 / x : ℝ) := by
      apply Finset.sum_le_sum
      intro n _
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx]
      exact div_le_div_of_nonneg_right (norm_logCoeff_le_one χ n) hx.le
    _ = (⌊x⌋₊ : ℝ) / x := by simp [div_eq_mul_inv]
    _ ≤ 1 := (div_le_one hx).mpr (Nat.floor_le hx.le)

lemma primesUpTo_eq_filter_Icc (N : ℕ) :
    primesUpTo N = (Finset.Icc 1 N).filter Nat.Prime := by
  ext n
  simp only [primesUpTo, Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
  constructor
  · intro h
    exact ⟨⟨h.2.one_le, by omega⟩, h.2⟩
  · intro h
    exact ⟨by omega, h.2⟩

lemma logCoeff_apply_prime {q p : ℕ} (χ : DirichletCharacter ℂ q) (hp : p.Prime) :
    logCoeff χ p = χ (p : ZMod q) := by
  have hlog : Real.log (p : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
  simp only [logCoeff, ArithmeticFunction.vonMangoldt_apply_prime hp]
  exact mul_div_cancel_right₀ _ (Complex.ofReal_ne_zero.mpr hlog)

lemma nonprime_reciprocalCoeff_norm_le {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) :
    ‖(if n.Prime then 0 else reciprocalCoeff χ n)‖ ≤
      OAI.SiegelZeros.W55.higherPrimePowerTerm n / Real.log 2 := by
  by_cases hp : n.Prime
  · simp [hp, OAI.SiegelZeros.W55.higherPrimePowerTerm]
  · simp only [hp, ↓reduceIte, OAI.SiegelZeros.W55.higherPrimePowerTerm]
    by_cases hn : 2 ≤ n
    · have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
      have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
      have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hlogs : Real.log 2 ≤ Real.log (n : ℝ) := Real.log_le_log (by norm_num) (by exact_mod_cast hn)
      rw [reciprocalCoeff, logCoeff, norm_div, norm_div, norm_mul,
        Complex.norm_natCast, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := n)),
        abs_of_pos hlog]
      have hΛ : 0 ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
      calc
        _ ≤ (ArithmeticFunction.vonMangoldt n / Real.log (n : ℝ)) / (n : ℝ) := by
          gcongr
          exact mul_le_of_le_one_left hΛ (χ.norm_le_one (n : ZMod q))
        _ = (ArithmeticFunction.vonMangoldt n / (n : ℝ)) / Real.log (n : ℝ) := by ring
        _ ≤ _ := div_le_div_of_nonneg_left (div_nonneg hΛ hnR.le) hlog2 hlogs
    · have hn' : n = 0 ∨ n = 1 := by omega
      rcases hn' with rfl | rfl <;> simp [reciprocalCoeff]

/-- The higher prime powers contribute a fixed absolute constant. -/
theorem prime_power_error_le {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ℝ) :
    ‖reciprocalMangoldtSum χ x - primeReciprocalSum χ x‖ ≤
      OAI.SiegelZeros.W55.higherPrimePowerConstant / Real.log 2 := by
  have heq : reciprocalMangoldtSum χ x - primeReciprocalSum χ x =
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, if n.Prime then 0 else reciprocalCoeff χ n := by
    rw [reciprocalMangoldtSum, primeReciprocalSum, primesUpTo_eq_filter_Icc,
      Finset.sum_filter, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _
    by_cases hp : n.Prime
    · simp [hp, reciprocalCoeff, logCoeff_apply_prime χ hp]
    · simp [hp]
  rw [heq]
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ‖if n.Prime then 0 else reciprocalCoeff χ n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, OAI.SiegelZeros.W55.higherPrimePowerTerm n / Real.log 2 :=
      Finset.sum_le_sum fun n _ => nonprime_reciprocalCoeff_norm_le χ n
    _ = (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, OAI.SiegelZeros.W55.higherPrimePowerTerm n) / Real.log 2 :=
      (Finset.sum_div _ _ _).symm
    _ ≤ _ := div_le_div_of_nonneg_right (OAI.SiegelZeros.W55.higherPrimePower_sum_le _)
      (Real.log_nonneg (by norm_num))

#print axioms desmoothing_error_le_one
#print axioms prime_power_error_le

end RealCharacterTail
