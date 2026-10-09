import ReflectedLiouville.PublishedInputs
import OAI.NumberTheory.DirichletL.Nonvanishing
import Mathlib.Tactic

set_option autoImplicit false

namespace ReflectedLiouville

/-- The 003 theorem removes every high-conductor zero in the KMT box.
    The principal pole is excluded by the literal conductor cutoff. -/
lemma kmt_good_modulus_of_zero_box (X u M : ℝ) (q : ℕ) [NeZero q]
    (hqX : (q : ℝ) ≤ X)
    (hcut : 1 ≤ Real.rpow X (Real.rpow u 20))
    (hleft : (7 / 8 : ℝ) < 1 - M * Real.log (Real.log X) / Real.log X) :
    KMTGoodModulus X u M q := by
  refine ⟨NeZero.pos q, hqX, ?_⟩
  intro χ hconductor s hs him
  apply OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re χ
    (hleft.trans_le hs)
  rintro ⟨hprincipal, hpole⟩
  rw [hprincipal, DirichletCharacter.conductor_one, Nat.cast_one] at hconductor
  linarith

lemma kmt_box_left_of_width (X M : ℝ)
    (hwidth : M * Real.log (Real.log X) / Real.log X < 1 / 8) :
    (7 / 8 : ℝ) < 1 - M * Real.log (Real.log X) / Real.log X := by
  linarith

#print axioms kmt_good_modulus_of_zero_box

end ReflectedLiouville
