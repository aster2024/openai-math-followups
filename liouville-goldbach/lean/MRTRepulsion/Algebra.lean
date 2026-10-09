import ReflectedLiouville.TwistRepulsion
import ReflectedLiouville.CharacterAlgebra
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTPrincipalSmallHeight

set_option autoImplicit false
open scoped BigOperators ComplexConjugate
open OAI.TwoPointCorrelations
open ReflectedLiouville

namespace MRTRepulsion

noncomputable def phaseSum (t : ℝ) (N : ℕ) : ℝ :=
  ∑ p ∈ primesUpTo N, (1 - Real.cos (t * Real.log (p : ℝ))) / (p : ℝ)

lemma phaseSum_nonneg (t : ℝ) (N : ℕ) : 0 ≤ phaseSum t N := by
  apply Finset.sum_nonneg
  intro p _
  exact div_nonneg (sub_nonneg.mpr (Real.cos_le_one _)) (Nat.cast_nonneg p)

lemma distance_formula (f : ℕ → ℂ) (hf : ∀ n, (f n).im = 0) (t : ℝ) (N : ℕ) :
    squaredDistance f (modulusOneTwist t) N =
      ∑ p ∈ primesUpTo N, (1 - (f p).re * Real.cos (t * Real.log (p : ℝ))) / p := by
  unfold squaredDistance
  apply Finset.sum_congr rfl
  intro p hp
  have hprime := (Finset.mem_filter.mp hp).2
  have he := mrt_principal_twist_re (q := 1) (by norm_num) hprime hprime.one_lt t
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, hf, zero_mul, sub_zero]
  rw [show (modulusOneTwist t p).re = Real.cos (t * Real.log (p : ℝ)) from he]

lemma real_part_bounds (f : ℕ → ℂ) (hf : OneBounded f) {p : ℕ} (hp : p.Prime) :
    -1 ≤ (f p).re ∧ (f p).re ≤ 1 := by
  exact abs_le.mp ((Complex.abs_re_le_norm _).trans (hf p hp.pos))

lemma double_angle_defect (a c : ℝ) (ha : -1 ≤ a ∧ a ≤ 1)
    (hc : -1 ≤ c ∧ c ≤ 1) :
    1 - (2 * c ^ 2 - 1) ≤ 4 * (1 - a * c) := by
  have ha2 : a ^ 2 ≤ 1 := by nlinarith [sq_nonneg (a+1),sq_nonneg (a-1)]
  nlinarith [sq_nonneg (a-c)]

lemma untwisted_defect (a c : ℝ) (ha : -1 ≤ a ∧ a ≤ 1)
    (hc : -1 ≤ c ∧ c ≤ 1) :
    1 - a ≤ 5 * (1 - a * c) + (2 * c ^ 2 - 1 - c) := by
  have hpos : 0 ≤ (1+a) * (2 * (1-c) * (2-c)) := by
    apply mul_nonneg (by linarith)
    exact mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by linarith)
  have hneg : 0 ≤ (1-a) * (2 * (c+1)^2) :=
    mul_nonneg (by linarith) (by positivity)
  nlinarith only [hpos,hneg]

lemma phaseSum_double_le (f : ℕ → ℂ) (hf : RealMultiplicative f) (t : ℝ) (N : ℕ) :
    phaseSum (2*t) N ≤ 4 * squaredDistance f (modulusOneTwist t) N := by
  rw [distance_formula f hf.2.2, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hprime := (Finset.mem_filter.mp hp).2
  have hc := abs_le.mp (Real.abs_cos_le_one (t * Real.log (p : ℝ)))
  have hh := double_angle_defect (f p).re _ (real_part_bounds f hf.2.1 hprime) hc
  have he : (2*t)*Real.log (p : ℝ) = 2*(t*Real.log (p : ℝ)) := by ring
  rw [he, Real.cos_two_mul, ← mul_div_assoc]
  exact div_le_div_of_nonneg_right hh (Nat.cast_nonneg p)

lemma untwisted_distance_le (f : ℕ → ℂ) (hf : RealMultiplicative f) (t : ℝ) (N : ℕ) :
    squaredDistance f (modulusOneTwist 0) N ≤
      5 * squaredDistance f (modulusOneTwist t) N + phaseSum t N - phaseSum (2*t) N := by
  rw [distance_formula f hf.2.2, distance_formula f hf.2.2]
  simp only [zero_mul,Real.cos_zero,mul_one]
  unfold phaseSum
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro p hp
  have hprime := (Finset.mem_filter.mp hp).2
  have hc := abs_le.mp (Real.abs_cos_le_one (t * Real.log (p : ℝ)))
  have hh := untwisted_defect (f p).re _ (real_part_bounds f hf.2.1 hprime) hc
  have he : (2*t)*Real.log (p : ℝ) = 2*(t*Real.log (p : ℝ)) := by ring
  rw [he,Real.cos_two_mul]
  convert div_le_div_of_nonneg_right hh (Nat.cast_nonneg p) using 1 <;> ring

#print axioms phaseSum_double_le
#print axioms untwisted_distance_le
end MRTRepulsion
