import ReflectedLiouville.AffineWindows
import ReflectedLiouville.RationalGrouping

set_option autoImplicit false
open scoped BigOperators
open OAI.TwoPointCorrelations

namespace ReflectedLiouville

noncomputable def rationalQuotientWindow (N q₀ r v h : ℕ) (a : ℤ) : ℂ :=
  ∑ m ∈ Finset.Icc (v + 1) (v + h),
    liouville (N * m + r) * additiveCharacter ((a : ℝ) / q₀) m

/-- The q₀ factor from rational-phase Cauchy is retained, and each grouped
    quotient class is the literal physical progression modulo N*q₀. -/
theorem rational_quotient_window_square (N q₀ r v h : ℕ) [NeZero N] [NeZero q₀] (a : ℤ) :
    ‖rationalQuotientWindow N q₀ r v h a‖ ^ (2 : ℕ) ≤
      (q₀ : ℝ) * ∑ b : ZMod q₀,
        ‖shortProgressionSum liouville (N * q₀) ((N * b.val + r : ℕ) : ZMod (N * q₀))
          ((N * v + r : ℕ) : ℝ) ((N * h : ℕ) : ℝ)‖ ^ (2 : ℕ) := by
  have hCauchy := rational_grouping_square_bound q₀ a (Finset.Icc (v + 1) (v + h))
    (fun m => liouville (N * m + r))
  have hphysical (b : ZMod q₀) :
      (∑ m ∈ (Finset.Icc (v + 1) (v + h)).filter (fun m : ℕ => (m : ZMod q₀) = b),
        liouville (N * m + r)) =
      shortProgressionSum liouville (N * q₀) ((N * b.val + r : ℕ) : ZMod (N * q₀))
        ((N * v + r : ℕ) : ℝ) ((N * h : ℕ) : ℝ) := by
    simpa only [ZMod.natCast_zmod_val] using
      quotient_class_window_physical liouville N q₀ r b.val v h (NeZero.pos N)
  change ‖rationalQuotientWindow N q₀ r v h a‖ ^ (2 : ℕ) ≤ _ at hCauchy
  simp only [hphysical] at hCauchy
  exact hCauchy

#print axioms rational_quotient_window_square

end ReflectedLiouville
