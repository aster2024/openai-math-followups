import ReflectedLiouville.QuotientResidues
import ReflectedLiouville.VarianceTransfer

set_option autoImplicit false

namespace ReflectedLiouville

lemma norm_square_close (z w : ℂ) (c : ℝ) (hc : 0 ≤ c) (hclose : ‖z - w‖ ≤ c) :
    ‖z‖ ^ (2 : ℕ) ≤ 2 * ‖w‖ ^ (2 : ℕ) + 2 * c ^ (2 : ℕ) := by
  have hsum : ‖z‖ ≤ ‖w‖ + ‖z - w‖ := by
    simpa only [add_sub_cancel] using norm_add_le w (z - w)
  have hsum' : ‖z‖ ≤ ‖w‖ + c := by linarith
  nlinarith [norm_nonneg z, norm_nonneg w, sq_nonneg (‖w‖ - c)]

lemma shifted_short_square_bound (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (q : ℕ) (a : ZMod q) (x y H : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hH : 0 ≤ H)
    (hd : |x - y| ≤ q) :
    ‖shortProgressionSum f q a x H‖ ^ (2 : ℕ) ≤
      2 * ‖shortProgressionSum f q a y H‖ ^ (2 : ℕ) + 8 := by
  have hclose := short_progression_start_shift f hf q a x y H hx hy hH hd
  have h := norm_square_close _ _ 2 (by norm_num) hclose
  norm_num at h
  exact h

lemma quotient_origin_distance (N v : ℕ) (r : Fin N) (s : ℝ) (hs0 : 0 ≤ s) (hsN : s ≤ N) :
    |((N * v + r.val + 1 : ℕ) : ℝ) - ((N * v : ℕ) : ℝ) - s| ≤ N := by
  have hr : (r.val : ℝ) + 1 ≤ N := by exact_mod_cast r.isLt
  have hr0 : (0 : ℝ) ≤ r.val := Nat.cast_nonneg _
  push_cast
  apply abs_le.mpr
  constructor <;> linarith

#print axioms shifted_short_square_bound

end ReflectedLiouville
