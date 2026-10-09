import ReflectedLiouville.SparseGraphTesting

set_option autoImplicit false
open scoped BigOperators Classical

namespace ReflectedLiouville

lemma operator_bilinear_half_energy {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →L[ℂ] H) (f g : H) :
    ‖inner ℂ f (A g)‖ ≤ ‖A‖ / 2 * (‖f‖ ^ 2 + ‖g‖ ^ 2) := by
  have hinner : ‖inner ℂ f (A g)‖ ≤ ‖f‖ * ‖A g‖ := norm_inner_le_norm f (A g)
  have hop := mul_le_mul_of_nonneg_left (A.le_opNorm g) (norm_nonneg f)
  have hs := mul_nonneg (norm_nonneg A) (sq_nonneg (‖f‖ - ‖g‖))
  apply hinner.trans
  apply hop.trans
  nlinarith only [hs]

/-- Good origins use operator compression and the total test energy. Bad
    origins use their sparse deterministic test bound and measured count. -/
theorem finite_good_bad_bilinear {Ω H : Type*} [Fintype Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : Ω → H →L[ℂ] H) (f g : Ω → H) (B D E ε : ℝ)
    (hB : 0 ≤ B) (hD : 0 ≤ D)
    (henergy : (∑ r, (‖f r‖ ^ 2 + ‖g r‖ ^ 2)) ≤ E)
    (hbadCount : (∑ r, if B < ‖A r‖ then (1 : ℝ) else 0) ≤ ε * Fintype.card Ω)
    (hbad : ∀ r, B < ‖A r‖ → ‖inner ℂ (f r) (A r (g r))‖ ≤ D) :
    (∑ r, ‖inner ℂ (f r) (A r (g r))‖) ≤ B / 2 * E + D * ε * Fintype.card Ω := by
  have hpoint (r : Ω) : ‖inner ℂ (f r) (A r (g r))‖ ≤
      B / 2 * (‖f r‖ ^ 2 + ‖g r‖ ^ 2) + D * (if B < ‖A r‖ then 1 else 0) := by
    by_cases hb : B < ‖A r‖
    · rw [ite_eq_left hb, mul_one]
      have he : 0 ≤ B / 2 * (‖f r‖ ^ 2 + ‖g r‖ ^ 2) := by positivity
      linarith only [hbad r hb, he]
    · rw [ite_eq_right hb, mul_zero, add_zero]
      have hn := operator_bilinear_half_energy (A r) (f r) (g r)
      apply hn.trans
      exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (le_of_not_gt hb) (by norm_num))
        (add_nonneg (sq_nonneg _) (sq_nonneg _))
  have he := mul_le_mul_of_nonneg_left henergy (by positivity : 0 ≤ B / 2)
  have hb := mul_le_mul_of_nonneg_left hbadCount hD
  calc
    _ ≤ ∑ r, (B / 2 * (‖f r‖ ^ 2 + ‖g r‖ ^ 2) + D * (if B < ‖A r‖ then 1 else 0)) :=
      Finset.sum_le_sum (fun r _ => hpoint r)
    _ = B / 2 * (∑ r, (‖f r‖ ^ 2 + ‖g r‖ ^ 2)) + D * (∑ r, if B < ‖A r‖ then 1 else 0) := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ _ := by nlinarith only [he, hb]

#print axioms finite_good_bad_bilinear

end ReflectedLiouville
