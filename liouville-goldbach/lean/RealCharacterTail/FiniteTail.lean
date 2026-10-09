import RealCharacterTail.Desmoothing

set_option autoImplicit false
open scoped BigOperators Topology
open Set Filter
open OAI.TwoPointCorrelations

namespace RealCharacterTail

/-- Strict real lower cutoffs agree with the difference of the two floor cutoffs. -/
theorem prime_tail_eq_difference {q : ℕ} (χ : DirichletCharacter ℂ q)
    {X Y : ℝ} (hY : 0 ≤ Y) (hYX : Y ≤ X) :
    (∑ p ∈ (primesUpTo ⌊X⌋₊).filter (fun p : ℕ => Y < (p : ℝ)),
      χ (p : ZMod q) / (p : ℂ)) = primeReciprocalSum χ X - primeReciprocalSum χ Y := by
  classical
  have hs : (primesUpTo ⌊X⌋₊).filter (fun p : ℕ => (p : ℝ) ≤ Y) = primesUpTo ⌊Y⌋₊ := by
    ext p
    simp only [Finset.mem_filter, primesUpTo, Finset.mem_range]
    constructor
    · rintro ⟨⟨hpx, hp⟩, hpy⟩
      have hpn := (Nat.le_floor_iff hY).mpr hpy
      exact ⟨by omega, hp⟩
    · rintro ⟨hpy, hp⟩
      have hpn : p ≤ ⌊Y⌋₊ := by omega
      have hpx := hpn.trans (Nat.floor_mono hYX)
      exact ⟨⟨by omega, hp⟩, (Nat.le_floor_iff hY).mp hpn⟩
  have hsplit : (∑ p ∈ (primesUpTo ⌊X⌋₊).filter (fun p : ℕ => (p : ℝ) ≤ Y),
        χ (p : ZMod q) / (p : ℂ)) +
      (∑ p ∈ (primesUpTo ⌊X⌋₊).filter (fun p : ℕ => Y < (p : ℝ)),
        χ (p : ZMod q) / (p : ℂ)) = primeReciprocalSum χ X := by
    rw [primeReciprocalSum, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp : (p : ℝ) ≤ Y
    · simp [hp, not_lt.mpr hp]
    · simp [hp, lt_of_not_ge hp]
  rw [hs] at hsplit
  change primeReciprocalSum χ Y + _ = primeReciprocalSum χ X at hsplit
  linear_combination hsplit

theorem real_prime_tail_le_norm {q : ℕ} (χ : DirichletCharacter ℂ q)
    {X Y : ℝ} (hY : 0 ≤ Y) (hYX : Y ≤ X) :
    |∑ p ∈ (primesUpTo ⌊X⌋₊).filter (fun p : ℕ => Y < (p : ℝ)),
      (χ (p : ZMod q)).re / p| ≤ ‖primeReciprocalSum χ X - primeReciprocalSum χ Y‖ := by
  have hr : (∑ p ∈ (primesUpTo ⌊X⌋₊).filter (fun p : ℕ => Y < (p : ℝ)),
      (χ (p : ZMod q)).re / p) =
      (∑ p ∈ (primesUpTo ⌊X⌋₊).filter (fun p : ℕ => Y < (p : ℝ)),
        χ (p : ZMod q) / (p : ℂ)).re := by
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro p _
    simp
  rw [hr]
  exact (Complex.abs_re_le_norm _).trans_eq (congrArg norm (prime_tail_eq_difference χ hY hYX))

#print axioms prime_tail_eq_difference
#print axioms real_prime_tail_le_norm

end RealCharacterTail
