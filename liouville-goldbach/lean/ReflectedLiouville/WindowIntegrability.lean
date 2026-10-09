import ReflectedLiouville.ShortSumIntegrability
import ReflectedLiouville.SharedOriginSquare

set_option autoImplicit false
open MeasureTheory
open scoped BigOperators

namespace ReflectedLiouville

lemma short_square_intervalIntegrable_on (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (q : ℕ) (a : ZMod q) (A B H : ℝ) (hAB : A ≤ B) (hH : 0 ≤ H) :
    IntervalIntegrable (fun x => ‖shortProgressionSum f q a x H‖ ^ (2 : ℕ)) volume A B := by
  have hm : Measurable (fun x => ‖shortProgressionSum f q a x H‖ ^ (2 : ℕ)) :=
    (shortProgressionSum_measurable f q a H hH).norm.pow_const 2
  let M : ℝ := (⌊B + H⌋₊ : ℝ)
  have hc : IntervalIntegrable (fun _x : ℝ => M ^ (2 : ℕ)) volume A B := intervalIntegrable_const
  apply hc.mono_fun' hm.stronglyMeasurable.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with x hx
  have hx' : x ∈ Set.Ioc A B := by simpa only [Set.uIoc_of_le hAB] using hx
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hbound := (shortProgressionSum_norm_le_floor f hf q a x H).trans
    (show (⌊x + H⌋₊ : ℝ) ≤ M by
      dsimp only [M]
      have hxy : x + H ≤ B + H := by linarith [hx'.2]
      exact_mod_cast Nat.floor_mono hxy)
  exact pow_le_pow_left₀ (norm_nonneg _) hbound 2

lemma allResidueSquares_intervalIntegrable_on (q : ℕ) [NeZero q]
    (A B H : ℝ) (hAB : A ≤ B) (hH : 0 ≤ H) :
    IntervalIntegrable (fun x => allResidueSquares q x H) volume A B := by
  have heq : (∑ a : ZMod q, fun x => ‖shortProgressionSum liouville q a x H‖ ^ (2 : ℕ)) =
      (fun x => allResidueSquares q x H) := by
    funext x
    simp only [Finset.sum_apply, allResidueSquares]
  rw [← heq]
  apply IntervalIntegrable.sum Finset.univ
  intro a ha
  exact short_square_intervalIntegrable_on liouville norm_liouville_le q a A B H hAB hH

lemma allResidueSquares_translated_intervalIntegrable (q : ℕ) [NeZero q]
    (x₀ T H : ℝ) (hT : 0 ≤ T) (hH : 0 ≤ H) :
    IntervalIntegrable (fun s => allResidueSquares q (x₀ + s) H) volume 0 T := by
  have h := allResidueSquares_intervalIntegrable_on q x₀ (x₀ + T) H (by linarith) hH
  have hc := h.comp_add_left x₀
  convert hc using 1 <;> simp

#print axioms allResidueSquares_translated_intervalIntegrable

end ReflectedLiouville
