import ReflectedLiouville.GcdResidues
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

set_option autoImplicit false
open scoped BigOperators

namespace ReflectedLiouville

noncomputable def reducedResidueEquivUnits (d : ℕ) [NeZero d] : ReducedResidues d ≃ (ZMod d)ˣ where
  toFun b := ZMod.unitOfCoprime b.val.val b.property
  invFun a := ⟨⟨(a : ZMod d).val, ZMod.val_lt _⟩, ZMod.val_coe_unit_coprime a⟩
  left_inv b := by
    apply Subtype.ext
    apply Fin.ext
    exact (ZMod.val_natCast_of_lt b.val.isLt)
  right_inv a := by
    apply Units.ext
    exact ZMod.natCast_zmod_val (a : ZMod d)

lemma reducedResidueEquivUnits_val (d : ℕ) [NeZero d] (b : ReducedResidues d) :
    ((reducedResidueEquivUnits d b : (ZMod d)ˣ) : ZMod d).val = b.val.val :=
  ZMod.val_natCast_of_lt b.val.isLt

lemma reduced_sum_eq_units (d : ℕ) [NeZero d] (F : ℕ → ℝ) :
    (∑ b : ReducedResidues d, F b.val.val) = ∑ a : (ZMod d)ˣ, F (a : ZMod d).val := by
  apply Fintype.sum_equiv (reducedResidueEquivUnits d)
  intro b
  rw [reducedResidueEquivUnits_val]

noncomputable def gcdResidueZModEquiv (q : ℕ) [NeZero q] : GcdResidueIndex q ≃ ZMod q :=
  Equiv.ofBijective (fun i => ((gcdResidueValue q i).val : ZMod q)) ⟨by
    intro i j heq
    apply gcdResidueValue_injective q
    apply Fin.ext
    have h := (ZMod.natCast_eq_natCast_iff' _ _ q).mp heq
    rwa [Nat.mod_eq_of_lt (gcdResidueValue q i).isLt,
      Nat.mod_eq_of_lt (gcdResidueValue q j).isLt] at h,
    by
    intro a
    obtain ⟨i, hi⟩ := gcdResidueValue_surjective q ⟨a.val, ZMod.val_lt a⟩
    refine ⟨i, ?_⟩
    have hv := congrArg Fin.val hi
    change ((gcdResidueValue q i).val : ZMod q) = a
    rw [hv, ZMod.natCast_zmod_val]⟩

/-- Finite gcd partition of every residue class, including zero and nonunits. -/
theorem sum_residues_by_gcd (q : ℕ) [NeZero q] (F : ZMod q → ℝ) :
    (∑ a : ZMod q, F a) =
      ∑ u : ↥q.divisors, ∑ b : ReducedResidues (q / u.val),
        F ((u.val * b.val.val : ℕ) : ZMod q) := by
  have h := (gcdResidueZModEquiv q).sum_comp F
  change (∑ i : GcdResidueIndex q, F ((i.1.val * i.2.val.val : ℕ) : ZMod q)) =
    ∑ a : ZMod q, F a at h
  rw [Fintype.sum_sigma] at h
  exact h.symm

#print axioms sum_residues_by_gcd

end ReflectedLiouville
