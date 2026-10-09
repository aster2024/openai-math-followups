import ReflectedLiouville.PublishedInputs
import ReflectedLiouville.Casts

set_option autoImplicit false
open scoped BigOperators ComplexConjugate
open OAI.TwoPointCorrelations

namespace ReflectedLiouville

lemma liouville_prime (p : ℕ) (hp : Nat.Prime p) : liouville p = -1 := by
  simp [OAI.TwoPointCorrelations.liouville, ArithmeticFunction.liouville_apply hp.ne_zero,
    ArithmeticFunction.cardFactors_apply_prime hp]

lemma modulusOneTwist_zero (n : ℕ) : modulusOneTwist 0 n = 1 := by
  have hn : (n : ZMod 1) = 1 := Subsingleton.elim _ _
  simp [modulusOneTwist, characterTwist, hn]

lemma liouville_realMultiplicative : RealMultiplicative liouville := by
  refine ⟨liouville_multiplicative, liouville_oneBounded, ?_⟩
  intro n
  rw [← liouvilleReal_cast]
  simp

lemma liouville_untwisted_distance (X : ℝ) :
    squaredDistance liouville (modulusOneTwist 0) ⌊X⌋₊ =
      2 * (∑ p ∈ primesUpTo ⌊X⌋₊, (1 : ℝ) / p) := by
  rw [Finset.mul_sum]
  unfold squaredDistance
  apply Finset.sum_congr rfl
  intro p hp
  have hprime : Nat.Prime p := (Finset.mem_filter.mp hp).2
  rw [liouville_prime p hprime, modulusOneTwist_zero]
  simp
  ring

lemma liouville_character_multiplicative {q : ℕ} (χ : DirichletCharacter ℂ q) :
    Multiplicative (fun n => liouville n * χ (n : ZMod q)) := by
  intro m n hm hn hcop
  simp only [liouville_mul, Nat.cast_mul, map_mul]
  ring

lemma liouville_one : liouville 1 = 1 := by
  simp [OAI.TwoPointCorrelations.liouville, ArithmeticFunction.liouville_apply_one]

lemma liouville_character_one {q : ℕ} (χ : DirichletCharacter ℂ q) :
    liouville 1 * χ (1 : ZMod q) = 1 := by rw [liouville_one, map_one, one_mul]

lemma liouville_character_complete {q : ℕ} (χ : DirichletCharacter ℂ q)
    (m n : ℕ) (_hm : 0 < m) (_hn : 0 < n) :
    liouville (m * n) * χ ((m * n : ℕ) : ZMod q) =
      (liouville m * χ (m : ZMod q)) * (liouville n * χ (n : ZMod q)) := by
  simp only [liouville_mul, Nat.cast_mul, map_mul]
  ring

lemma liouville_character_oneBounded {q : ℕ} (χ : DirichletCharacter ℂ q) :
    OneBounded (fun n => liouville n * χ (n : ZMod q)) := by
  intro n hn
  rw [norm_mul]
  exact (mul_le_mul (norm_liouville_le n) (χ.norm_le_one _)
    (norm_nonneg _) zero_le_one).trans_eq (by norm_num)

lemma liouville_character_realMultiplicative {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hχ : RealCharacter χ) :
    RealMultiplicative (fun n => liouville n * χ (n : ZMod q)) := by
  refine ⟨liouville_character_multiplicative χ, liouville_character_oneBounded χ, ?_⟩
  intro n
  change (liouville n * χ (n : ZMod q)).im = 0
  rw [← liouvilleReal_cast n, Complex.mul_im, Complex.ofReal_im, hχ]
  simp

/-- The exact prime expansion, before any analytic prime-sum estimate. -/
lemma liouville_character_untwisted_distance {q : ℕ} (χ : DirichletCharacter ℂ q) (X : ℝ) :
    squaredDistance (fun n => liouville n * χ (n : ZMod q)) (modulusOneTwist 0) ⌊X⌋₊ =
      (∑ p ∈ primesUpTo ⌊X⌋₊, (1 : ℝ) / p) +
      (∑ p ∈ primesUpTo ⌊X⌋₊, (χ (p : ZMod q)).re / p) := by
  rw [← Finset.sum_add_distrib]
  unfold squaredDistance
  apply Finset.sum_congr rfl
  intro p hp
  have hprime : Nat.Prime p := (Finset.mem_filter.mp hp).2
  change (1 - (liouville p * χ (p : ZMod q) * conj (modulusOneTwist 0 p)).re) / (p : ℝ) =
    (1 : ℝ) / p + (χ (p : ZMod q)).re / p
  rw [liouville_prime p hprime, modulusOneTwist_zero]
  simp only [map_one, mul_one, neg_one_mul, Complex.neg_re]
  ring

#print axioms liouville_character_untwisted_distance

end ReflectedLiouville
