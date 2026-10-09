import ReflectedLiouville.GcdSums
import ReflectedLiouville.UnitProgressionVariance

set_option autoImplicit false
open scoped BigOperators

namespace ReflectedLiouville

lemma quotient_divisor_ne_zero (q : ℕ) [NeZero q] (u : ↥q.divisors) : q / u.val ≠ 0 := by
  intro hd
  have h := divisor_mul_quotient q u
  rw [hd, Nat.mul_zero] at h
  exact NeZero.ne q h.symm

lemma norm_liouville_of_positive (u : ℕ) (hu : 0 < u) : ‖liouville u‖ = 1 := by
  rw [← liouvilleReal_cast, Complex.norm_real, Real.norm_eq_abs]
  exact abs_liouvilleReal hu.ne'

lemma scaled_short_square (q : ℕ) [NeZero q] (u : ↥q.divisors)
    (b : ℕ) (x H : ℝ) (hH : 0 ≤ H) :
    ‖shortProgressionSum liouville q ((u.val * b : ℕ) : ZMod q) x H‖ ^ (2 : ℕ) =
      ‖shortProgressionSum liouville (q / u.val) (b : ZMod (q / u.val)) (x / u.val) (H / u.val)‖ ^ (2 : ℕ) := by
  have hs := shortProgressionSum_scaling u.val (q / u.val) b (divisor_positive q u) x H hH
  rw [divisor_mul_quotient] at hs
  rw [hs, norm_mul, norm_liouville_of_positive u.val (divisor_positive q u), one_mul]

noncomputable def unitResidueSquares (q : ℕ) [NeZero q] (x H : ℝ) : ℝ :=
  ∑ a : (ZMod q)ˣ, ‖shortProgressionSum liouville q (a : ZMod q) x H‖ ^ (2 : ℕ)

/-- The exact pointwise decomposition of all residue-class energies into gcd
    strata. This equality includes zero and all nonunit residue classes. -/
theorem all_residue_squares_gcd (q : ℕ) [NeZero q] (x H : ℝ) (hH : 0 ≤ H) :
    (∑ a : ZMod q, ‖shortProgressionSum liouville q a x H‖ ^ (2 : ℕ)) =
      ∑ u : ↥q.divisors,
        letI : NeZero (q / u.val) := ⟨quotient_divisor_ne_zero q u⟩
        unitResidueSquares (q / u.val) (x / u.val) (H / u.val) := by
  rw [sum_residues_by_gcd]
  apply Finset.sum_congr rfl
  intro u hu
  letI : NeZero (q / u.val) := ⟨quotient_divisor_ne_zero q u⟩
  calc
    _ = ∑ b : ReducedResidues (q / u.val),
        ‖shortProgressionSum liouville (q / u.val) (b.val.val : ZMod (q / u.val))
          (x / u.val) (H / u.val)‖ ^ (2 : ℕ) := by
      apply Finset.sum_congr rfl
      intro b hb
      exact scaled_short_square q u b.val.val x H hH
    _ = ∑ a : (ZMod (q / u.val))ˣ,
        ‖shortProgressionSum liouville (q / u.val) ((a : ZMod (q / u.val)).val : ZMod (q / u.val))
          (x / u.val) (H / u.val)‖ ^ (2 : ℕ) :=
      reduced_sum_eq_units (q / u.val) (fun n : ℕ =>
        ‖shortProgressionSum liouville (q / u.val) (n : ZMod (q / u.val))
          (x / u.val) (H / u.val)‖ ^ (2 : ℕ))
    _ = _ := by simp only [ZMod.natCast_zmod_val, unitResidueSquares]

#print axioms all_residue_squares_gcd

end ReflectedLiouville
