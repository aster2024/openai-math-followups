import ReflectedLiouville.TwistRepulsion
import OAI.NumberTheory.TwoPoint.Halasz.HalaszMeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

set_option autoImplicit false
open Filter
open OAI.TwoPointCorrelations

namespace ReflectedLiouville

lemma archimedean_twist_eq_modulusOne (t : ℝ) : mrtArchimedeanTwist t = modulusOneTwist t := by
  funext n
  have hn : (n : ZMod 1) = 1 := Subsingleton.elim _ _
  simp [mrtArchimedeanTwist, modulusOneTwist, characterTwist, hn]

lemma floor_log_comparison (X : ℝ) (hX : 4 ≤ X) :
    1 ≤ Real.log X ∧ 0 < Real.log (⌊X⌋₊ : ℝ) ∧
      Real.log X ≤ 2 * Real.log (⌊X⌋₊ : ℝ) := by
  have hN2 : (2 : ℕ) ≤ ⌊X⌋₊ := (Nat.le_floor_iff (by linarith)).mpr (by norm_num; linarith)
  have hN2r : (2 : ℝ) ≤ ⌊X⌋₊ := by exact_mod_cast hN2
  have hNp : (0 : ℝ) < ⌊X⌋₊ := by linarith
  have hhalf : X ≤ 2 * (⌊X⌋₊ : ℝ) := by
    have hfloor := Nat.lt_floor_add_one X
    linarith
  have hlogN : Real.log 2 ≤ Real.log (⌊X⌋₊ : ℝ) := Real.log_le_log (by norm_num) hN2r
  have hlogX := Real.log_le_log (by linarith : (0 : ℝ) < X) hhalf
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hNp.ne'] at hlogX
  have hlog4 : 1 ≤ Real.log (4 : ℝ) := by
    have h : Real.log 2 ≥ (1 / 2 : ℝ) := by
      have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at h
      exact h
    have heq : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      simpa only [Real.log_pow, Nat.cast_ofNat] using congrArg Real.log (show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num)
    linarith
  refine ⟨hlog4.trans (Real.log_le_log (by norm_num) hX), Real.log_pos (by linarith), ?_⟩
  linarith

lemma eventually_library_halasz_height :
    ∀ᶠ N : ℕ in atTop, (Real.log (N : ℝ)) ^ (8 : ℕ) ≤ (N : ℝ) := by
  have h := (Real.tendsto_exp_div_pow_atTop 8).comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [h.eventually (eventually_ge_atTop (1 : ℝ)),
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (1 : ℝ)), eventually_ge_atTop (1 : ℕ)] with N hbound hlog hN
  change 1 ≤ Real.exp (Real.log (N : ℝ)) / (Real.log (N : ℝ)) ^ (8 : ℕ) at hbound
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  rw [Real.exp_log hNp] at hbound
  simpa only [one_mul] using (le_div_iff₀ (by positivity : (0 : ℝ) < (Real.log (N : ℝ)) ^ (8 : ℕ))).mp hbound

lemma eventually_loglog_error :
    ∀ᶠ X : ℝ in atTop,
      Real.log (Real.log X) / Real.log X ≤ (Real.log X) ^ (-1 / 40 : ℝ) := by
  have hlim := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 39 / 40)).tendsto_div_nhds_zero
  have hlim' := hlim.comp Real.tendsto_log_atTop
  filter_upwards [hlim'.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1)),
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with X hX hlog
  change Real.log (Real.log X) / (Real.log X) ^ (39 / 40 : ℝ) ≤ 1 at hX
  have hbound := (div_le_iff₀ (Real.rpow_pos_of_pos hlog (39 / 40))).mp hX
  apply (div_le_iff₀ hlog).mpr
  have heq : (Real.log X) ^ (-1 / 40 : ℝ) * Real.log X = (Real.log X) ^ (39 / 40 : ℝ) := by
    conv_lhs => rhs; rw [← Real.rpow_one (Real.log X)]
    rw [← Real.rpow_add hlog]
    congr 1
    norm_num
  rw [heq]
  simpa only [one_mul] using hbound

lemma floor_loglog_error (X : ℝ) (hX : 4 ≤ X) :
    Real.log (Real.log (⌊X⌋₊ : ℝ)) / Real.log (⌊X⌋₊ : ℝ) ≤
      2 * (Real.log (Real.log X) / Real.log X) := by
  obtain ⟨hlogX, hlogN, hcompare⟩ := floor_log_comparison X hX
  have hXp : 0 < X := by linarith
  have hNpos : (0 : ℝ) < ⌊X⌋₊ := by
    have hfloor2 : (2 : ℕ) ≤ ⌊X⌋₊ := (Nat.le_floor_iff (by linarith)).mpr (by norm_num; linarith)
    exact_mod_cast (by omega : 0 < ⌊X⌋₊)
  have hlogNX := Real.log_le_log hNpos (Nat.floor_le hXp.le)
  have hllNX := Real.log_le_log hlogN hlogNX
  have hllX : 0 ≤ Real.log (Real.log X) := Real.log_nonneg hlogX
  calc
    _ ≤ Real.log (Real.log X) / Real.log (⌊X⌋₊ : ℝ) :=
      div_le_div_of_nonneg_right hllNX hlogN.le
    _ ≤ Real.log (Real.log X) / (Real.log X / 2) :=
      div_le_div_of_nonneg_left hllX (by linarith) (by linarith)
    _ = _ := by ring

#print axioms archimedean_twist_eq_modulusOne

end ReflectedLiouville
