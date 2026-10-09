import ReflectedLiouville.TwistRepulsion
import ReflectedLiouville.HalaszScales
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false
open Filter
open scoped BigOperators
open OAI.TwoPointCorrelations

namespace ReflectedLiouville

lemma halaszMinimum_ge (f : ℕ → ℂ) (X T M : ℝ) (hT : 0 ≤ T)
    (hlower : ∀ t : ℝ, |t| ≤ T → M ≤ squaredDistance f (modulusOneTwist t) ⌊X⌋₊) :
    M ≤ halaszMinimum f X T := by
  unfold halaszMinimum
  apply le_csInf
  · refine ⟨squaredDistance f (modulusOneTwist 0) ⌊X⌋₊, 0, ?_, rfl⟩
    simpa only [abs_zero] using hT
  · rintro v ⟨t, ht, rfl⟩
    exact hlower t ht

lemma halasz_exponential_error (X M : ℝ) (hlog : 1 ≤ Real.log X)
    (hM : Real.log (Real.log X) / 32 ≤ M) :
    (M + 1) * Real.exp (-M) ≤ 10 * (Real.log X) ^ (-1 / 40 : ℝ) := by
  have hlogp : 0 < Real.log X := by linarith
  have hpoly : M + 1 ≤ 10 * Real.exp (M / 10) := by
    have h := Real.add_one_le_exp (M / 10)
    linarith
  calc
    _ ≤ (10 * Real.exp (M / 10)) * Real.exp (-M) :=
      mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le
    _ = 10 * Real.exp (-(9 / 10 : ℝ) * M) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ 10 * Real.exp (-(9 / 320 : ℝ) * Real.log (Real.log X)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Real.exp_le_exp.mpr (by linarith)
    _ = 10 * (Real.log X) ^ (-9 / 320 : ℝ) := by
      rw [Real.rpow_def_of_pos hlogp]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hlog (by norm_num)) (by norm_num)

lemma reciprocal_fourth_root (x : ℝ) (hx : 0 ≤ x) :
    1 / Real.sqrt (Real.sqrt x) = x ^ (-1 / 4 : ℝ) := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hx]
  norm_num
  exact (Real.rpow_neg hx (1 / 4)).symm

lemma halasz_full_error (X M : ℝ) (hlog : 1 ≤ Real.log X)
    (hM : Real.log (Real.log X) / 32 ≤ M) :
    (M + 1) * Real.exp (-M) + 1 / Real.sqrt (Real.sqrt (Real.log X)) +
      Real.rpow (Real.log X) (-1 / 4) ≤ 12 * (Real.log X) ^ (-1 / 40 : ℝ) := by
  rw [reciprocal_fourth_root _ (by linarith)]
  have hsmall : (Real.log X) ^ (-1 / 4 : ℝ) ≤ (Real.log X) ^ (-1 / 40 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hlog (by norm_num)
  have hexp := halasz_exponential_error X M hlog hM
  simpa only [Real.rpow_eq_pow] using (by linarith :
    (M + 1) * Real.exp (-M) + (Real.log X) ^ (-1 / 4 : ℝ) +
      (Real.log X) ^ (-1 / 4 : ℝ) ≤ 12 * (Real.log X) ^ (-1 / 40 : ℝ))

/-- The proved library Halasz theorem and published MRT repulsion yield this
    mean bound for normalized completely multiplicative real functions.
    The untwisted distance is a derived target, not a published assumption. -/
theorem real_mean_of_untwisted_distance
    (h_MRT : MRTRealTwistRepulsionInput) :
    ∃ C X₀ : ℝ, 0 < C ∧ 100 ≤ X₀ ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ f : ℕ → ℂ, RealMultiplicative f →
        f 1 = 1 → (∀ m n : ℕ, 0 < m → 0 < n → f (m * n) = f m * f n) →
        Real.log (Real.log X) / 2 ≤ squaredDistance f (modulusOneTwist 0) ⌊X⌋₊ →
        ‖∑ n ∈ Finset.Icc 1 ⌊X⌋₊, f n‖ ≤ C * X / Real.rpow (Real.log X) (1 / 40) := by
  obtain ⟨C, Y₀, hC, hhalasz⟩ := halasz_mean_value
  obtain ⟨X₁, hX₁, htwist⟩ := mrt_uniform_twist_lower_bound h_MRT
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp eventually_library_halasz_height
  obtain ⟨X₂, hX₂⟩ := eventually_atTop.mp eventually_loglog_error
  let K := max N₀ ⌈Y₀⌉₊
  refine ⟨12 * C, max X₁ (max ((K : ℝ) + 1) X₂), by positivity,
    hX₁.trans (le_max_left _ _), ?_⟩
  intro X hX f hf hf1 hfcomplete hbase
  have hXX₁ : X₁ ≤ X := (le_max_left _ _).trans hX
  have hX100 : 100 ≤ X := hX₁.trans hXX₁
  have hXp : 0 < X := by linarith
  have hKX : (K : ℝ) ≤ X := by
    have h := (le_max_left _ _).trans ((le_max_right _ _).trans hX)
    linarith
  have hKN : K ≤ ⌊X⌋₊ := (Nat.le_floor_iff hXp.le).mpr hKX
  have hN₀N : N₀ ≤ ⌊X⌋₊ := (le_max_left _ _).trans hKN
  have hY₀N : Y₀ ≤ (⌊X⌋₊ : ℝ) := (Nat.le_ceil _).trans (by
    exact_mod_cast (le_max_right N₀ ⌈Y₀⌉₊).trans hKN)
  have hheight := (hN₀ ⌊X⌋₊ hN₀N).trans (Nat.floor_le hXp.le)
  obtain ⟨hlog, hlogN, hlogCompare⟩ := floor_log_comparison X (by linarith)
  have hdist : ∀ t ∈ Set.Icc (-(Real.log (⌊X⌋₊ : ℝ) ^ (8 : ℕ)))
      (Real.log (⌊X⌋₊ : ℝ) ^ (8 : ℕ)),
      Real.log (Real.log X) / 32 ≤ squaredDistance f (mrtArchimedeanTwist t) ⌊X⌋₊ := by
    intro t ht
    rw [archimedean_twist_eq_modulusOne]
    exact htwist X hXX₁ f hf hbase t ((abs_le.mpr ht).trans hheight)
  let M := Real.log (Real.log X) / 32
  have hM : 0 ≤ M := div_nonneg (Real.log_nonneg hlog) (by norm_num)
  have hbound := hhalasz ⌊X⌋₊ hY₀N f hf1 hfcomplete hf.2.1 M hM hdist
  have hexp := halasz_exponential_error X M hlog le_rfl
  have hXX₂ : X₂ ≤ X := (le_max_right _ _).trans ((le_max_right _ _).trans hX)
  have herr := (floor_loglog_error X (by linarith)).trans
    (mul_le_mul_of_nonneg_left (hX₂ X hXX₂) (by norm_num : (0 : ℝ) ≤ 2))
  have htotal : (M + 1) * Real.exp (-M) + Real.log (Real.log (⌊X⌋₊ : ℝ)) /
      Real.log (⌊X⌋₊ : ℝ) ≤ 12 * (Real.log X) ^ (-1 / 40 : ℝ) := by linarith
  calc
    _ ≤ C * (⌊X⌋₊ : ℝ) * (12 * (Real.log X) ^ (-1 / 40 : ℝ)) :=
      hbound.trans (mul_le_mul_of_nonneg_left htotal (by positivity))
    _ ≤ C * X * (12 * (Real.log X) ^ (-1 / 40 : ℝ)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Nat.floor_le hXp.le) hC.le) (by positivity)
    _ = _ := by
      simp only [Real.rpow_eq_pow]
      rw [show (-1 / 40 : ℝ) = -(1 / 40 : ℝ) by ring]
      rw [Real.rpow_neg (by linarith : 0 ≤ Real.log X)]
      ring

#print axioms real_mean_of_untwisted_distance

end ReflectedLiouville
