import ReflectedLiouville.FiniteCauchy
import OAI.NumberTheory.TwoPoint.Bounds.ProgressionFourier

set_option autoImplicit false
open scoped BigOperators
open OAI.TwoPointCorrelations

namespace ReflectedLiouville

lemma stdAddChar_int_mul (q : ℕ) [NeZero q] (a : ℤ) (n : ℕ) :
    ZMod.stdAddChar ((a : ZMod q) * (n : ZMod q)) = additiveCharacter ((a : ℝ) / q) n := by
  have heq : (a : ZMod q) * (n : ZMod q) = ((a * (n : ℤ) : ℤ) : ZMod q) := by simp
  rw [heq, ZMod.stdAddChar_coe]
  unfold additiveCharacter
  congr 1
  push_cast
  field_simp <;> ring

lemma rational_phase_norm (q : ℕ) [NeZero q] (a : ℤ) (b : ZMod q) :
    ‖ZMod.stdAddChar ((a : ZMod q) * b)‖ = 1 := by
  rw [ZMod.stdAddChar_apply, Circle.norm_coe]

lemma residue_grouping (q : ℕ) [NeZero q] (S : Finset ℕ) (f : ℕ → ℂ) (c : ZMod q → ℂ) :
    (∑ n ∈ S, f n * c (n : ZMod q)) =
      ∑ b : ZMod q, c b * (∑ n ∈ S.filter (fun n : ℕ => (n : ZMod q) = b), f n) := by
  classical
  simp only [Finset.mul_sum, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  simp [mul_comm]

theorem rational_grouping_square_bound (q : ℕ) [NeZero q] (a : ℤ) (S : Finset ℕ) (f : ℕ → ℂ) :
    ‖∑ n ∈ S, f n * additiveCharacter ((a : ℝ) / q) n‖ ^ (2 : ℕ) ≤
      (q : ℝ) * ∑ b : ZMod q,
        ‖∑ n ∈ S.filter (fun n : ℕ => (n : ZMod q) = b), f n‖ ^ (2 : ℕ) := by
  simp_rw [← stdAddChar_int_mul q a]
  rw [residue_grouping q S f (fun b : ZMod q => ZMod.stdAddChar ((a : ZMod q) * b))]
  have h := finite_complex_cauchy (Finset.univ : Finset (ZMod q))
    (fun b => ZMod.stdAddChar ((a : ZMod q) * b) *
      (∑ n ∈ S.filter (fun n : ℕ => (n : ZMod q) = b), f n))
  simpa only [Finset.card_univ, ZMod.card, norm_mul, rational_phase_norm, one_mul] using h

#print axioms rational_grouping_square_bound

end ReflectedLiouville
