import ReflectedLiouville.ProgressionShift
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

set_option autoImplicit false
open scoped BigOperators

namespace ReflectedLiouville

lemma finEquiv_cast (q : ℕ) [NeZero q] (a : Fin q) :
    ZMod.finEquiv q a = (a.val : ZMod q) := by
  cases q with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ q =>
    apply Fin.ext
    change a.val = (a.val : ZMod (q + 1)).val
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt a.isLt]

/-- The quotient coordinates use r+1, so the last class Q is the zero residue. -/
noncomputable def quotientResidueEquiv (N q₀ : ℕ) [NeZero N] [NeZero q₀] :
    (Fin q₀ × Fin N) ≃ ZMod (N * q₀) :=
  ((finProdFinEquiv.trans (finCongr (Nat.mul_comm q₀ N))).trans (ZMod.finEquiv (N * q₀)).toEquiv).trans
    (Equiv.addRight (1 : ZMod (N * q₀)))

lemma quotientResidueEquiv_apply (N q₀ : ℕ) [NeZero N] [NeZero q₀]
    (br : Fin q₀ × Fin N) :
    quotientResidueEquiv N q₀ br = ((N * br.1.val + br.2.val + 1 : ℕ) : ZMod (N * q₀)) := by
  change ZMod.finEquiv (N * q₀) (finCongr (Nat.mul_comm q₀ N) (finProdFinEquiv br)) + 1 = _
  rw [finEquiv_cast]
  change (((br.2.val + N * br.1.val : ℕ) : ZMod (N * q₀)) + 1) = _
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
  ring

theorem quotient_residue_sum (N q₀ : ℕ) [NeZero N] [NeZero q₀] (F : ZMod (N * q₀) → ℝ) :
    (∑ b : Fin q₀, ∑ r : Fin N, F ((N * b.val + r.val + 1 : ℕ) : ZMod (N * q₀))) =
      ∑ a : ZMod (N * q₀), F a := by
  have h := (quotientResidueEquiv N q₀).sum_comp F
  simp only [quotientResidueEquiv_apply, Fintype.sum_prod_type] at h
  exact h

#print axioms quotient_residue_sum

end ReflectedLiouville
