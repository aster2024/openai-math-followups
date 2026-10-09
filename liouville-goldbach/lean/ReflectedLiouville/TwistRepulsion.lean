import ReflectedLiouville.PublishedInputs
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

set_option autoImplicit false
open Filter
open scoped BigOperators ComplexConjugate
open OAI.TwoPointCorrelations

namespace ReflectedLiouville

lemma squaredDistance_twist_nonneg (f : ℕ → ℂ) (hf : OneBounded f) (t : ℝ) (N : ℕ) :
    0 ≤ squaredDistance f (modulusOneTwist t) N := by
  unfold squaredDistance
  apply Finset.sum_nonneg
  intro p hp
  have hprime := (Finset.mem_filter.mp hp).2
  have hnorm : ‖f p * conj (modulusOneTwist t p)‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_conj]
    have htwist := characterTwist_norm_le_one (1 : DirichletCharacter ℂ 1) t p
    exact (mul_le_mul (hf p hprime.pos) htwist (norm_nonneg _) zero_le_one).trans_eq
      (by norm_num)
  apply div_nonneg _ (Nat.cast_nonneg p)
  exact sub_nonneg.mpr ((Complex.re_le_norm _).trans hnorm)

/-- Elementary quantified margin for the two square-root estimates of MRT C.1. -/
lemma square_root_repulsion_margin (T C D₀ D : ℝ)
    (hC : 0 ≤ C) (hT : 10000 * C ^ 2 + 1 ≤ T)
    (hD₀ : T / 2 ≤ D₀) (hD : 0 ≤ D)
    (hsmall : (1 / 3 : ℝ) * Real.sqrt D₀ - C ≤ Real.sqrt D) :
    T / 32 ≤ D := by
  have hT₀ : 0 ≤ T := by nlinarith
  have hD₀₀ : 0 ≤ D₀ := by linarith
  have hsqT := Real.sq_sqrt hT₀
  have hsqD₀ := Real.sq_sqrt hD₀₀
  have hsqD := Real.sq_sqrt hD
  have hroot₀ : (2 / 3 : ℝ) * Real.sqrt T ≤ Real.sqrt D₀ := by
    apply (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
    nlinarith
  have hCroot : C ≤ Real.sqrt T / 100 := by
    have hroot : 100 * C ≤ Real.sqrt T := by
      apply (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
      nlinarith
    linarith
  have hroot : Real.sqrt T / 5 ≤ Real.sqrt D := by linarith
  have hsq := (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg D)).mpr hroot
  nlinarith

lemma square_root_large_repulsion_margin (T C D : ℝ)
    (hC : 0 ≤ C) (hT : 10000 * C ^ 2 + 1 ≤ T) (hD : 0 ≤ D)
    (hlarge : (1 / 4 : ℝ) * Real.sqrt T - C ≤ Real.sqrt D) :
    T / 32 ≤ D := by
  have hT₀ : 0 ≤ T := by nlinarith
  have hsqT := Real.sq_sqrt hT₀
  have hsqD := Real.sq_sqrt hD
  have hCroot : C ≤ Real.sqrt T / 100 := by
    have hroot : 100 * C ≤ Real.sqrt T := by
      apply (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
      nlinarith
    linarith
  have hroot : Real.sqrt T / 5 ≤ Real.sqrt D := by linarith
  have hsq := (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg D)).mpr hroot
  nlinarith

/-- MRT supplies one uniform twist lower bound once the untwisted distance
    has the project's separately derived lower bound. -/
theorem mrt_uniform_twist_lower_bound (h_MRT : MRTRealTwistRepulsionInput) :
    ∃ X₀ : ℝ, 100 ≤ X₀ ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ f : ℕ → ℂ, RealMultiplicative f →
        Real.log (Real.log X) / 2 ≤ squaredDistance f (modulusOneTwist 0) ⌊X⌋₊ →
        ∀ t : ℝ, |t| ≤ X →
          Real.log (Real.log X) / 32 ≤ squaredDistance f (modulusOneTwist t) ⌊X⌋₊ := by
  obtain ⟨C, hC, hrep⟩ := h_MRT
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.mp
    ((Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually
      (eventually_ge_atTop (10000 * C ^ 2 + 1)))
  refine ⟨max 100 X₁, le_max_left _ _, ?_⟩
  intro X hX f hf hbase t ht
  have hX100 : 100 ≤ X := (le_max_left _ _).trans hX
  have hX1 : X₁ ≤ X := (le_max_right _ _).trans hX
  have hT := hX₁ X hX1
  have hD := squaredDistance_twist_nonneg f hf.2.1 t ⌊X⌋₊
  by_cases ht1 : 1 ≤ |t|
  · exact square_root_large_repulsion_margin _ C _ hC.le hT hD
      ((hrep f hf X hX100 t).1 ht1 ht)
  · exact square_root_repulsion_margin _ C _ _ hC.le hT hbase hD
      ((hrep f hf X hX100 t).2 (le_of_lt (lt_of_not_ge ht1)))

#print axioms mrt_uniform_twist_lower_bound

end ReflectedLiouville
