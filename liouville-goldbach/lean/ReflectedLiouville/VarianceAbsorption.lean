import ReflectedLiouville.TotientUniform
import ReflectedLiouville.UnitVariance
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false
open Filter

namespace ReflectedLiouville

lemma eventually_loglog_power_error (k : ℕ) (a b C : ℝ) (hba : b < a) :
    ∀ᶠ X : ℝ in atTop,
      C * (Real.log (Real.log X)) ^ k * (Real.log X) ^ (-a) ≤ (Real.log X) ^ (-b) := by
  have hlim := (isLittleO_log_rpow_rpow_atTop (k : ℝ) (sub_pos.mpr hba)).tendsto_div_nhds_zero
  have h := ((tendsto_const_nhds (x := C)).mul hlim).comp Real.tendsto_log_atTop
  filter_upwards [h.eventually (eventually_le_nhds (by simp : C * (0 : ℝ) < 1)),
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with X hX hlog
  change C * ((Real.log (Real.log X)) ^ (k : ℝ) / (Real.log X) ^ (a - b)) ≤ 1 at hX
  rw [Real.rpow_natCast] at hX
  have hratio : C * (Real.log (Real.log X)) ^ k / (Real.log X) ^ (a - b) ≤ 1 := by
    simpa only [mul_div_assoc] using hX
  have hmain := (div_le_iff₀ (Real.rpow_pos_of_pos hlog (a - b))).mp hratio
  have hmul := mul_le_mul_of_nonneg_right hmain (Real.rpow_nonneg hlog.le (-a))
  have hid : (Real.log X) ^ (a - b) * (Real.log X) ^ (-a) = (Real.log X) ^ (-b) := by
    rw [← Real.rpow_add hlog]
    congr 1
    ring
  simpa only [one_mul, hid] using hmul

lemma eventually_main_character_ratio_small (D : ℝ) :
    ∀ᶠ X : ℝ in atTop, ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ X →
      D ^ 2 * ((q : ℝ) / q.totient) ^ 2 / (Real.log X) ^ (1 / 20 : ℝ) ≤
        (Real.log X) ^ (-1 / 1000 : ℝ) := by
  obtain ⟨A, hA, hratio⟩ := totient_ratio_uniform
  filter_upwards [eventually_loglog_power_error 4 (1 / 20) (1 / 1000) (D ^ 2 * A ^ 2) (by norm_num),
    eventually_ge_atTop (Real.exp 2)] with X hsmall hX
  intro q inst hqX
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  have hφ : (0 : ℝ) ≤ q.totient := Nat.cast_nonneg _
  have hsquared := pow_le_pow_left₀ (div_nonneg hq hφ) (hratio X hX q hqX) 2
  have hsquared' : ((q : ℝ) / q.totient) ^ 2 ≤ A ^ 2 * (Real.log (Real.log X)) ^ (4 : ℕ) := by
    convert hsquared using 1 <;> ring
  have hlog : 0 < Real.log X := by
    have h := Real.log_le_log (Real.exp_pos 2) hX
    rw [Real.log_exp] at h
    linarith
  calc
    _ ≤ D ^ 2 * (A ^ 2 * (Real.log (Real.log X)) ^ (4 : ℕ)) / (Real.log X) ^ (1 / 20 : ℝ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsquared' (sq_nonneg D)) (by positivity)
    _ = (D ^ 2 * A ^ 2) * (Real.log (Real.log X)) ^ (4 : ℕ) * (Real.log X) ^ (-(1 / 20 : ℝ)) := by
      rw [Real.rpow_neg hlog.le]
      ring
    _ ≤ _ := by simpa only [neg_div] using hsmall

lemma main_energy_normalization (D X H : ℝ) (q : ℕ) [NeZero q] :
    D ^ 2 * X * H ^ 2 / ((q.totient : ℝ) * (Real.log X) ^ (1 / 20 : ℝ)) =
      (D ^ 2 * ((q : ℝ) / q.totient) ^ 2 / (Real.log X) ^ (1 / 20 : ℝ)) *
        ((q.totient : ℝ) * X * (H / q) ^ 2) := by
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q
  ring_nf
  field_simp

/-- The unit-class variance has the target ε scale whenever the reviewed KMT
    range is derived. h_tail is the realmean module's derived target. -/
theorem kmt_unit_variance_saved
    (h_KMT : KMTInput) (h_MRT : MRTRealTwistRepulsionInput)
    (h_tail : RealCharacterPrimeTailBound) :
    ∃ C X₀ : ℝ, 0 < C ∧ 10 ≤ X₀ ∧ ∀ X H Q : ℝ, X₀ ≤ X →
      ∀ (q : ℕ) [NeZero q], 1 < H / q → H / q ≤ X →
        KMTRange X H Q ((Real.log (H / q)) ^ (-1 / 1000 : ℝ)) q →
        unitResidueVariance q X H ≤ C * ((Real.log (H / q)) ^ (-1 / 1000 : ℝ)) *
          (q.totient : ℝ) * X * (H / q) ^ 2 := by
  obtain ⟨C, D, X₁, hC, hD, hX₁, hunit⟩ := kmt_unit_variance_uncentered h_KMT h_MRT h_tail
  obtain ⟨X₂, hX₂⟩ := eventually_atTop.mp (eventually_main_character_ratio_small D)
  refine ⟨2 * C + 2, max X₁ X₂, by positivity, hX₁.trans (le_max_left _ _), ?_⟩
  intro X H Q hX q inst hR hRX hrange
  have hXX₁ : X₁ ≤ X := (le_max_left _ _).trans hX
  have hXX₂ : X₂ ≤ X := (le_max_right _ _).trans hX
  have hXpos : 0 < X := by linarith
  have hqX : (q : ℝ) ≤ X := hrange.good.2.1
  have hsmall := hX₂ X hXX₂ q hqX
  have hε : (Real.log X) ^ (-1 / 1000 : ℝ) ≤ (Real.log (H / q)) ^ (-1 / 1000 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos (Real.log_pos hR)
      (Real.log_le_log (by linarith : 0 < H / q) hRX) (by norm_num)
  have henergy := mul_le_mul_of_nonneg_right (hsmall.trans hε)
    (by positivity : 0 ≤ (q.totient : ℝ) * X * (H / q) ^ 2)
  rw [← main_energy_normalization] at henergy
  have h := hunit X H Q ((Real.log (H / q)) ^ (-1 / 1000 : ℝ)) hXX₁ q hrange
  simp only [Real.rpow_eq_pow] at h
  have henergy2 := mul_le_mul_of_nonneg_left henergy (by norm_num : (0 : ℝ) ≤ 2)
  have henergy2' : 2 * D ^ 2 * X * H ^ 2 / ((q.totient : ℝ) * (Real.log X) ^ (1 / 20 : ℝ)) ≤
      2 * (((Real.log (H / q)) ^ (-1 / 1000 : ℝ)) * ((q.totient : ℝ) * X * (H / q) ^ 2)) := by
    convert henergy2 using 1 <;> ring
  calc
    _ ≤ 2 * C * ((Real.log (H / q)) ^ (-1 / 1000 : ℝ)) * (q.totient : ℝ) * X * (H / q) ^ 2 +
        2 * (((Real.log (H / q)) ^ (-1 / 1000 : ℝ)) * ((q.totient : ℝ) * X * (H / q) ^ 2)) := by
      exact h.trans (add_le_add le_rfl henergy2')
    _ = _ := by ring

#print axioms kmt_unit_variance_saved

end ReflectedLiouville
