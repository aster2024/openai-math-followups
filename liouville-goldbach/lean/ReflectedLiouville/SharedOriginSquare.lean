import ReflectedLiouville.QuotientWindowSquare
import ReflectedLiouville.WindowSquareShift

set_option autoImplicit false
open scoped BigOperators

namespace ReflectedLiouville

lemma quotient_residue_sum_common (N q₀ : ℕ) [NeZero N] [NeZero q₀] (F : ZMod (N * q₀) → ℝ) :
    (∑ r : Fin N, ∑ b : ZMod q₀, F ((N * b.val + r.val + 1 : ℕ) : ZMod (N * q₀))) =
      ∑ a : ZMod (N * q₀), F a := by
  have hQ' : ∀ G : ZMod (N * q₀) → ℝ,
      (∑ b : Fin q₀, ∑ r : Fin N, G ((N * b.val + r.val + 1 : ℕ) : ZMod (N * q₀))) =
        ∑ a : ZMod (N * q₀), G a := by
    exact quotient_residue_sum N q₀
  have hFin : (∑ b : Fin q₀, ∑ r : Fin N, F ((N * b.val + r.val + 1 : ℕ) : ZMod (N * q₀))) =
      ∑ b : ZMod q₀, ∑ r : Fin N, F ((N * b.val + r.val + 1 : ℕ) : ZMod (N * q₀)) := by
    apply Fintype.sum_equiv (ZMod.finEquiv q₀).toEquiv
    intro b
    change (∑ r : Fin N, F ((N * b.val + r.val + 1 : ℕ) : ZMod (N * q₀))) =
      ∑ r : Fin N, F ((N * (ZMod.finEquiv q₀ b).val + r.val + 1 : ℕ) : ZMod (N * q₀))
    rw [finEquiv_cast, ZMod.val_natCast_of_lt b.isLt]
  rw [Finset.sum_comm]
  exact hFin.symm.trans (hQ' F)

noncomputable def allResidueSquares (q : ℕ) [NeZero q] (x H : ℝ) : ℝ :=
  ∑ a : ZMod q, ‖shortProgressionSum liouville q a x H‖ ^ (2 : ℕ)

/-- The pointwise discrete-origin-to-common-origin bound, with explicit error
    8*N*q₀² from the two endpoint shifts. -/
theorem rational_window_shared_origin (N q₀ v h : ℕ) [NeZero N] [NeZero q₀]
    (a : ℤ) (s : ℝ) (hs0 : 0 ≤ s) (hsN : s ≤ N) :
    (∑ r : Fin N, ‖rationalQuotientWindow N q₀ (r.val + 1) v h a‖ ^ (2 : ℕ)) ≤
      2 * (q₀ : ℝ) * allResidueSquares (N * q₀) (((N * v : ℕ) : ℝ) + s) ((N * h : ℕ) : ℝ) +
        8 * (N : ℝ) * (q₀ : ℝ) ^ (2 : ℕ) := by
  have hNQ : (N : ℝ) ≤ ((N * q₀ : ℕ) : ℝ) := by
    exact_mod_cast (Nat.le_mul_of_pos_right N (NeZero.pos q₀))
  have hpoint (r : Fin N) (b : ZMod q₀) :
      ‖shortProgressionSum liouville (N * q₀) ((N * b.val + r.val + 1 : ℕ) : ZMod (N * q₀))
        ((N * v + r.val + 1 : ℕ) : ℝ) ((N * h : ℕ) : ℝ)‖ ^ (2 : ℕ) ≤
      2 * ‖shortProgressionSum liouville (N * q₀) ((N * b.val + r.val + 1 : ℕ) : ZMod (N * q₀))
        (((N * v : ℕ) : ℝ) + s) ((N * h : ℕ) : ℝ)‖ ^ (2 : ℕ) + 8 := by
    apply shifted_short_square_bound liouville norm_liouville_le
      (N * q₀) _ _ _ _ (by positivity) (by positivity) (by positivity)
    have hd := quotient_origin_distance N v r s hs0 hsN
    simpa only [sub_add_eq_sub_sub] using hd.trans hNQ
  have hquot (r : Fin N) := rational_quotient_window_square N q₀ (r.val + 1) v h a
  have hstep : (∑ r : Fin N, ‖rationalQuotientWindow N q₀ (r.val + 1) v h a‖ ^ (2 : ℕ)) ≤
      (q₀ : ℝ) * ∑ r : Fin N, ∑ b : ZMod q₀,
        (2 * ‖shortProgressionSum liouville (N * q₀) ((N * b.val + r.val + 1 : ℕ) : ZMod (N * q₀))
          (((N * v : ℕ) : ℝ) + s) ((N * h : ℕ) : ℝ)‖ ^ (2 : ℕ) + 8) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro r hr
    have h := hquot r
    simp only [← Nat.add_assoc] at h
    apply h.trans
    exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun b _ => hpoint r b)) (Nat.cast_nonneg q₀)
  have hsum := quotient_residue_sum_common N q₀ (fun z =>
    ‖shortProgressionSum liouville (N * q₀) z (((N * v : ℕ) : ℝ) + s) ((N * h : ℕ) : ℝ)‖ ^ (2 : ℕ))
  apply hstep.trans_eq
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, ZMod.card, nsmul_eq_mul]
  rw [hsum]
  unfold allResidueSquares
  ring

#print axioms rational_window_shared_origin

end ReflectedLiouville
