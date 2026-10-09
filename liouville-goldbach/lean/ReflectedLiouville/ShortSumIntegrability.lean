import ReflectedLiouville.ShortSums
import ReflectedLiouville.Casts
import Mathlib.Tactic

set_option autoImplicit false
open MeasureTheory
open scoped BigOperators

namespace ReflectedLiouville

lemma shortProgressionSum_norm_le_floor (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (q : ℕ) (a : ZMod q) (x H : ℝ) :
    ‖shortProgressionSum f q a x H‖ ≤ (⌊x + H⌋₊ : ℝ) := by
  classical
  unfold shortProgressionSum
  calc
    _ ≤ ∑ n ∈ (Finset.Icc (⌊x⌋₊ + 1) ⌊x + H⌋₊).filter (fun n : ℕ => (n : ZMod q) = a), ‖f n‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _n ∈ (Finset.Icc (⌊x⌋₊ + 1) ⌊x + H⌋₊).filter (fun n : ℕ => (n : ZMod q) = a), (1 : ℝ) :=
      Finset.sum_le_sum (fun n _ => hf n)
    _ ≤ (⌊x + H⌋₊ : ℝ) := by
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      have hcard := Finset.card_le_card
        (Finset.filter_subset (fun n : ℕ => (n : ZMod q) = a) (Finset.Icc (⌊x⌋₊ + 1) ⌊x + H⌋₊))
      have hI : (Finset.Icc (⌊x⌋₊ + 1) ⌊x + H⌋₊).card ≤ ⌊x + H⌋₊ := by
        rw [Nat.card_Icc]
        omega
      exact_mod_cast hcard.trans hI

lemma shortProgressionSum_norm_bound_on (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (q : ℕ) (a : ZMod q) (X H x : ℝ) (hx : x ≤ 2 * X) :
    ‖shortProgressionSum f q a x H‖ ≤ (⌊2 * X + H⌋₊ : ℝ) :=
  (shortProgressionSum_norm_le_floor f hf q a x H).trans
    (by exact_mod_cast Nat.floor_mono (by linarith : x + H ≤ 2 * X + H))

/-- Concrete square integrability, including subtraction of an arbitrary fixed
    character main term. No analytic theorem supplies this property. -/
lemma shortProgressionSum_square_intervalIntegrable (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (q : ℕ) (a : ZMod q) (X H : ℝ) (hX : 0 ≤ X) (hH : 0 ≤ H) (w : ℂ) :
    IntervalIntegrable (fun x : ℝ => ‖shortProgressionSum f q a x H - w‖ ^ 2) volume X (2 * X) := by
  have hm : Measurable (fun x : ℝ => ‖shortProgressionSum f q a x H - w‖ ^ 2) :=
    ((shortProgressionSum_measurable f q a H hH).sub_const w).norm.pow_const 2
  let M : ℝ := (⌊2 * X + H⌋₊ : ℝ) + ‖w‖
  have hconstant : IntervalIntegrable (fun _x : ℝ => M ^ 2) volume X (2 * X) := intervalIntegrable_const
  apply hconstant.mono_fun' hm.stronglyMeasurable.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with x hx
  have hx' : x ∈ Set.Ioc X (2 * X) := by
    simpa only [Set.uIoc_of_le (by linarith : X ≤ 2 * X)] using hx
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hnorm : ‖shortProgressionSum f q a x H - w‖ ≤ M := by
    apply (norm_sub_le _ _).trans
    exact add_le_add (shortProgressionSum_norm_bound_on f hf q a X H x hx'.2) le_rfl
  exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2

lemma liouville_short_square_intervalIntegrable (q : ℕ) (a : ZMod q) (X H : ℝ)
    (hX : 0 ≤ X) (hH : 0 ≤ H) (w : ℂ) :
    IntervalIntegrable (fun x : ℝ => ‖shortProgressionSum liouville q a x H - w‖ ^ 2)
      volume X (2 * X) :=
  shortProgressionSum_square_intervalIntegrable liouville norm_liouville_le q a X H hX hH w

#print axioms shortProgressionSum_square_intervalIntegrable

end ReflectedLiouville
