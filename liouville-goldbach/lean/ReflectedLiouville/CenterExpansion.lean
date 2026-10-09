import ReflectedLiouville.ReflectedForms
import OAI.NumberTheory.TwoPoint.Bounds.CenterBandExpansion

set_option autoImplicit false
open scoped BigOperators Classical
open OAI.TwoPointCorrelations

namespace ReflectedLiouville

/-- Exact cast of the paper's real centered factor into the library's finite
    expansion; natural and signed-integer divisibility are identified. -/
lemma centeredTuple_cast_nat (S : Finset ℕ) (n : ℕ) :
    (centeredTuple S (n : ℤ) : ℂ) =
      ∏ p ∈ S, (natDivisibilityIndicator p n - 1 / (p : ℂ)) := by
  unfold centeredTuple
  rw [Complex.ofReal_prod]
  apply Finset.prod_congr rfl
  intro p hp
  by_cases hd : p ∣ n
  · have hdi : (p : ℤ) ∣ (n : ℤ) := by exact_mod_cast hd
    simp only [hdi, ite_true, natDivisibilityIndicator, hd, Complex.ofReal_sub, Complex.ofReal_one,
      Complex.ofReal_inv, Complex.ofReal_natCast, one_div]
  · have hdi : ¬(p : ℤ) ∣ (n : ℤ) := by intro h; exact hd (by exact_mod_cast h)
    simp only [hdi, ite_false, natDivisibilityIndicator, hd, Complex.ofReal_sub, Complex.ofReal_zero,
      Complex.ofReal_inv, Complex.ofReal_natCast, one_div]

theorem centered_tuple_subset_expansion (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (n : ℕ) :
    (centeredTuple S (n : ℤ) : ℂ) =
      ∑ W ∈ S.powerset, ((-1 : ℂ) ^ W.card / ((∏ p ∈ W, p : ℕ) : ℂ)) *
        natDivisibilityIndicator (∏ p ∈ S \ W, p) n := by
  rw [centeredTuple_cast_nat]
  exact centerBand_expansion S hS 1 n

/-- The empty subset is precisely the raw divisibility term; every remaining
    term has one reciprocal mean-prime product and complementary divisibility. -/
theorem centering_nonempty_subset_difference (d n : ℕ) (hd : Squarefree d) :
    natDivisibilityIndicator d n - (centeredTuple d.primeFactors (n : ℤ) : ℂ) =
      -(∑ W ∈ d.primeFactors.powerset.erase ∅,
        ((-1 : ℂ) ^ W.card / ((∏ p ∈ W, p : ℕ) : ℂ)) *
          natDivisibilityIndicator (∏ p ∈ d.primeFactors \ W, p) n) := by
  have hprime : ∀ p ∈ d.primeFactors, p.Prime := fun p hp => (Nat.mem_primeFactors.mp hp).1
  have hExpansion := centered_tuple_subset_expansion d.primeFactors hprime n
  let f := fun W : Finset ℕ => ((-1 : ℂ) ^ W.card / ((∏ p ∈ W, p : ℕ) : ℂ)) *
    natDivisibilityIndicator (∏ p ∈ d.primeFactors \ W, p) n
  have hempty : (∅ : Finset ℕ) ∈ d.primeFactors.powerset := by simp
  have hsum := Finset.sum_erase_add d.primeFactors.powerset f hempty
  have hzero : f ∅ = natDivisibilityIndicator d n := by
    simp [f, Nat.prod_primeFactors_of_squarefree hd]
  rw [hzero] at hsum
  change (centeredTuple d.primeFactors (n : ℤ) : ℂ) = ∑ W ∈ d.primeFactors.powerset, f W at hExpansion
  change natDivisibilityIndicator d n - (centeredTuple d.primeFactors (n : ℤ) : ℂ) =
    -(∑ W ∈ d.primeFactors.powerset.erase ∅, f W)
  linear_combination hsum - hExpansion

#print axioms centering_nonempty_subset_difference

end ReflectedLiouville
