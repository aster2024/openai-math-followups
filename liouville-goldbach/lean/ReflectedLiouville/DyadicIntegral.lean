import ReflectedLiouville.WindowIntegrability
import Mathlib.Algebra.Order.Archimedean.Basic

set_option autoImplicit false
open MeasureTheory
open scoped BigOperators

namespace ReflectedLiouville

lemma dyadic_integral_sum (f : ℝ → ℝ) (H : ℝ) (hH : 0 ≤ H)
    (hInt : ∀ A B : ℝ, A ≤ B → IntervalIntegrable f volume A B) (k : ℕ) :
    (∑ i ∈ Finset.range k, ∫ x in (2 : ℝ) ^ i * H..(2 : ℝ) ^ (i + 1) * H, f x) =
      ∫ x in H..(2 : ℝ) ^ k * H, f x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    have hge : H ≤ (2 : ℝ) ^ k * H := le_mul_of_one_le_left hH
      (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) : 1 ≤ (2 : ℝ) ^ k)
    have hstep : (2 : ℝ) ^ k * H ≤ (2 : ℝ) ^ (k + 1) * H := by
      rw [pow_succ]
      nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) k]
    exact intervalIntegral.integral_add_adjacent_intervals (hInt _ _ hge) (hInt _ _ hstep)

lemma dyadic_left_end_sum (H : ℝ) (k : ℕ) :
    (∑ i ∈ Finset.range k, (2 : ℝ) ^ i * H) = ((2 : ℝ) ^ k - 1) * H := by
  induction k with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring

/-- Cover a nonnegative integrable function by dyadic intervals with total
    left-endpoint mass at most 2Y. -/
theorem dyadic_integral_upper (f : ℝ → ℝ) (H Y B : ℝ) (hH : 0 < H) (hHY : H ≤ Y) (hB : 0 ≤ B)
    (hInt : ∀ A Z : ℝ, A ≤ Z → IntervalIntegrable f volume A Z)
    (hf : ∀ x : ℝ, 0 ≤ f x)
    (hcell : ∀ X : ℝ, H ≤ X → X ≤ Y → (∫ x in X..2 * X, f x) ≤ B * X) :
    (∫ x in H..Y, f x) ≤ 2 * B * Y := by
  have hratio : 1 ≤ Y / H := (le_div_iff₀ hH).mpr (by linarith)
  obtain ⟨n, hnlo, hnhi⟩ := exists_nat_pow_near hratio (by norm_num : (1 : ℝ) < 2)
  have hnY : (2 : ℝ) ^ n * H ≤ Y := (le_div_iff₀ hH).mp hnlo
  have hYnext : Y ≤ (2 : ℝ) ^ (n + 1) * H := ((div_lt_iff₀ hH).mp hnhi).le
  have hnextY : (2 : ℝ) ^ (n + 1) * H ≤ 2 * Y := by rw [pow_succ]; nlinarith
  have hmono := intervalIntegral.integral_mono_interval le_rfl hHY hYnext
    (Filter.Eventually.of_forall hf) (hInt H ((2 : ℝ) ^ (n + 1) * H) (hHY.trans hYnext))
  rw [← dyadic_integral_sum f H hH.le hInt (n + 1)] at hmono
  have hsum : (∑ i ∈ Finset.range (n + 1), ∫ x in (2 : ℝ) ^ i * H..(2 : ℝ) ^ (i + 1) * H, f x) ≤
      B * (∑ i ∈ Finset.range (n + 1), (2 : ℝ) ^ i * H) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hin : i ≤ n := by have h := Finset.mem_range.mp hi; omega
    have hlo : H ≤ (2 : ℝ) ^ i * H := le_mul_of_one_le_left hH.le
      (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) : 1 ≤ (2 : ℝ) ^ i)
    have hhi : (2 : ℝ) ^ i * H ≤ Y :=
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hin) hH.le).trans hnY
    have h := hcell ((2 : ℝ) ^ i * H) hlo hhi
    have heq : (2 : ℝ) ^ (i + 1) * H = 2 * ((2 : ℝ) ^ i * H) := by rw [pow_succ]; ring
    rwa [← heq] at h
  apply hmono.trans (hsum.trans _)
  rw [dyadic_left_end_sum]
  nlinarith

#print axioms dyadic_integral_upper

end ReflectedLiouville
