import ReflectedLiouville.PrimeCounting
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false
open Filter
open OAI.TwoPointCorrelations

namespace ReflectedLiouville

lemma eventually_exponential_prime_count (θ : ℝ) (hθ : 0 < θ) :
    ∀ᶠ X : ℝ in atTop,
      100 * Real.log X / Real.log 2 ≤
        ((primesUpTo ⌊Real.exp ((Real.log X) ^ θ)⌋₊).card : ℝ) := by
  have hpower := (tendsto_rpow_atTop hθ).comp Real.tendsto_log_atTop
  have hE := Real.tendsto_exp_atTop.comp hpower
  have hG := (tendsto_exp_div_rpow_atTop (1 + 1 / θ)).comp hpower
  filter_upwards [hE.eventually eventually_prime_count_lower,
    hG.eventually (eventually_ge_atTop (400 / Real.log 2)),
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with X hP hG hlog
  change Real.exp ((Real.log X) ^ θ) / (4 * Real.log (Real.exp ((Real.log X) ^ θ))) ≤
    ((primesUpTo ⌊Real.exp ((Real.log X) ^ θ)⌋₊).card : ℝ) at hP
  rw [Real.log_exp] at hP
  change 400 / Real.log 2 ≤ Real.exp ((Real.log X) ^ θ) /
    ((Real.log X) ^ θ) ^ (1 + 1 / θ) at hG
  have hden : ((Real.log X) ^ θ) ^ (1 + 1 / θ) = (Real.log X) ^ (θ + 1) := by
    rw [← Real.rpow_mul hlog.le]
    congr 1
    field_simp
  rw [hden] at hG
  have hmain := (le_div_iff₀ (Real.rpow_pos_of_pos hlog (θ + 1))).mp hG
  have hid : Real.log X * (Real.log X) ^ θ = (Real.log X) ^ (θ + 1) := by
    conv_lhs => lhs; rw [← Real.rpow_one (Real.log X)]
    rw [← Real.rpow_add hlog]
    congr 1
    ring
  apply le_trans _ hP
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * (Real.log X) ^ θ)).mpr
  calc
    _ = (400 / Real.log 2) * (Real.log X * (Real.log X) ^ θ) := by ring
    _ = (400 / Real.log 2) * (Real.log X) ^ (θ + 1) := by rw [hid]
    _ ≤ _ := hmain

/-- All moduli q≤X are typical once the cutoff is exp((log X)^θ).
    This supplies the precise Definition 1.1 premise, including every z≥y. -/
theorem all_moduli_eventually_typical (θ : ℝ) (hθ : 0 < θ) :
    ∀ᶠ X : ℝ in atTop, ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ X →
      KMTTypical q (Real.exp ((Real.log X) ^ θ)) := by
  filter_upwards [eventually_exponential_prime_count θ hθ] with X hcount
  intro q inst hqX
  have hqp : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hlogqX := Real.log_le_log hqp hqX
  have hcard : (q.primeFactors.card : ℝ) ≤ Real.log X / Real.log 2 :=
    (prime_factor_count_le_log q).trans
      (div_le_div_of_nonneg_right hlogqX (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le)
  have hcount' : 100 * (q.primeFactors.card : ℝ) ≤
      ((primesUpTo ⌊Real.exp ((Real.log X) ^ θ)⌋₊).card : ℝ) := by
    have h := (mul_le_mul_of_nonneg_left hcard (by norm_num : (0 : ℝ) ≤ 100)).trans
      (by simpa only [mul_div_assoc] using hcount)
    exact h
  apply kmt_typical_of_prime_count
  exact_mod_cast hcount'

lemma KMTTypical.mono_cutoff {q : ℕ} {y z : ℝ} (h : KMTTypical q y) (hyz : y ≤ z) : KMTTypical q z :=
  fun t ht => h t (hyz.trans ht)

#print axioms all_moduli_eventually_typical

end ReflectedLiouville
