import ReflectedLiouville.ReflectedForms
import ReflectedLiouville.Casts
import ReflectedLiouville.CenterExpansion

set_option autoImplicit false
open scoped BigOperators Classical
open OAI.TwoPointCorrelations

namespace ReflectedLiouville

lemma int_cast_sub_toNat (a n : ℕ) : ((a : ℤ) - (n : ℤ)).toNat = a - n := by omega

lemma liouvilleAtInteger_cast_nat (n : ℕ) : (liouvilleAtInteger (n : ℤ) : ℂ) = liouville n := by
  simp only [liouvilleAtInteger, Int.toNat_natCast, liouvilleReal_cast]

lemma liouvilleAtInteger_cast_difference (a n : ℕ) :
    (liouvilleAtInteger ((a : ℤ) - (n : ℤ)) : ℂ) = liouville (a - n) := by
  simp only [liouvilleAtInteger, int_cast_sub_toNat, liouvilleReal_cast]

lemma centeredReflectionAtom_cast_nat (N d q n : ℕ) :
    (centeredReflectionAtom N (d,q) (n : ℤ) : ℂ) =
      (actualPaddingCoefficient q : ℂ) * natDivisibilityIndicator q n *
        (centeredTuple d.primeFactors (n : ℤ) : ℂ) * liouville n * liouville (N * (q * d) - n) := by
  have hprod : N * d * q = N * (q * d) := by ring
  have hdv : (q : ℤ) ∣ (n : ℤ) ↔ q ∣ n := by exact_mod_cast (Iff.rfl : q ∣ n ↔ q ∣ n)
  unfold centeredReflectionAtom
  dsimp only [Prod.fst, Prod.snd]
  rw [hprod]
  by_cases hq : q ∣ n
  · simp only [hdv, hq, ite_true, natDivisibilityIndicator, Complex.ofReal_mul,
      liouvilleAtInteger_cast_nat, liouvilleAtInteger_cast_difference, mul_one]
  · simp only [hdv, hq, ite_false, natDivisibilityIndicator, Complex.ofReal_zero, mul_zero, zero_mul]

#print axioms centeredReflectionAtom_cast_nat
end ReflectedLiouville
