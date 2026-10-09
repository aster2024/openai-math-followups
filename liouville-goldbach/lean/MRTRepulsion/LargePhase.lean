import MRTRepulsion.PrimePhase
import OAI.NumberTheory.TwoPoint.Halasz.HalaszWeakHurwitzTheorem
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTWeakVKApplications

set_option autoImplicit false
open scoped BigOperators Classical
open OAI.TwoPointCorrelations
open Finset Filter

namespace MRTRepulsion

lemma principal_tail_cosine (u a : ℝ) (N : ℕ) :
    (∑ p ∈ mrtPrimePowerTail a N,
      characterTwist (1 : DirichletCharacter ℂ 1) u p / (p : ℂ)).re =
    ∑ p ∈ mrtPrimePowerTail a N, Real.cos (u*Real.log (p : ℝ)) / p := by
  simp only [Complex.re_sum]
  apply sum_congr rfl
  intro p hp
  rw [show (p : ℂ) = ((p : ℝ) : ℂ) by simp,Complex.div_ofReal_re]
  exact congrArg (fun x : ℝ => x/(p : ℝ))
    (mrt_principal_twist_re (q := 1) (by norm_num) (mrtPrimeBand_prime hp)
      (mrtPrimeBand_prime hp).one_lt u)

/-- The pinned OAI library already proves the weak Hurwitz growth input.
    Its power-logarithmic prime tail with exponent 3/4 is sufficient here. -/
theorem large_phase_lower : ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ N : ℕ in atTop, ∀ u : ℝ, 1 ≤ |u| → |u| ≤ 6*(N : ℝ) →
      Real.log (Real.log (N : ℝ))/4 - C ≤ phaseSum u N := by
  obtain ⟨C,T,hC,hT,htail⟩ := mrt_weak_hurwitz_growth.power_prime_tail
    (by norm_num : (2/3 : ℝ) < 3/4) (by norm_num)
  obtain ⟨D,hD,hmass⟩ := mrt_prime_power_tail_mass
  obtain ⟨c,K,hc,hK,hlow⟩ := modFiveThetaInput.halasz_prime_phase_lower
  let E : ℝ := (8+T)*K
  have hE : 0 ≤ E := by dsimp [E]; positivity
  refine ⟨C+D+3+E,by positivity,?_⟩
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [htail,hlog.eventually (eventually_ge_atTop (1 : ℝ))]
    with N hn hL
  intro u hu huN
  have hN : Real.exp 1 ≤ (N : ℝ) := by
    have hp : 0 < (N : ℝ) :=
      zero_lt_one.trans ((Real.log_pos_iff (Nat.cast_nonneg N)).mp (by linarith))
    exact (Real.exp_le_exp.mpr hL).trans_eq (Real.exp_log hp)
  have hLL : 0 ≤ Real.log (Real.log (N : ℝ)) := Real.log_nonneg hL
  by_cases hh : T ≤ |u|
  · have hq : (1 : ℝ) ≤ (Real.log (N : ℝ))^(1/125 : ℝ) :=
      Real.one_le_rpow hL (by norm_num)
    have hp := hn 1 (by simpa using hq) (1 : DirichletCharacter ℂ 1) u hh huN
    rw [principal_tail_cosine] at hp
    have hm := hmass (3/4) (by norm_num) (by norm_num) N hL
    have he : bandPhase u (Real.exp ((Real.log (N : ℝ))^(3/4 : ℝ))) N =
        (∑ p ∈ mrtPrimePowerTail (3/4) N, 1/(p : ℝ)) -
          ∑ p ∈ mrtPrimePowerTail (3/4) N, Real.cos (u*Real.log (p : ℝ))/p := by
      rw [← sum_sub_distrib]
      apply sum_congr rfl
      intro p _
      ring
    have hf := bandPhase_le_phaseSum u
      (Real.exp ((Real.log (N : ℝ))^(3/4 : ℝ))) N (Real.exp_pos _).le
    rw [he] at hf
    have hcosp := (abs_le.mp hp).2
    norm_num only [show (1 : ℝ)-3/4=1/4 by norm_num] at hm
    linarith only [hm,hf,hcosp,hE]
  · have hl := hlow (Real.exp 1) N u le_rfl hN (by simpa only [Real.log_exp,mul_one] using hu)
    simp only [Real.log_exp,div_one,Real.sqrt_one,mul_one] at hl
    have he : (8+|u|)*K*Real.exp (-c) ≤ E := by
      have hexp : Real.exp (-c) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      apply (mul_le_mul_of_nonneg_left hexp (by positivity : 0 ≤ (8+|u|)*K)).trans
      dsimp [E]
      simpa only [mul_one] using mul_le_mul_of_nonneg_right (by linarith [le_of_not_ge hh]) hK
    have hf := bandPhase_le_phaseSum u (Real.exp 1) N (Real.exp_pos 1).le
    change _ ≤ bandPhase u (Real.exp 1) N at hl
    linarith only [hl,he,hf,hLL,hC,hD]

#print axioms large_phase_lower
end MRTRepulsion
