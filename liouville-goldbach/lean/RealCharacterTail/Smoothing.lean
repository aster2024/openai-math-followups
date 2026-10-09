import RealCharacterTail.EulerLog
import OAI.NumberTheory.TwoPoint.Fourier.ModFiveSmoothedPsi

set_option autoImplicit false
open scoped BigOperators Topology
open Set Filter Finset MeasureTheory Complex Erdos970
open OAI.TwoPointCorrelations

namespace RealCharacterTail

noncomputable def reciprocalCoeff {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  logCoeff χ n / (n : ℂ)

noncomputable def smoothedReciprocalSum {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, reciprocalCoeff χ n * ((1 - (n : ℝ) / x : ℝ) : ℂ)

/-- The shifted Euler series has the reciprocal coefficients. -/
theorem reciprocal_series_shift {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) :
    LSeries (reciprocalCoeff χ) s = LSeries (logCoeff χ) (s + 1) := by
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · subst n
    simp
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
    have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    rw [Complex.cpow_add _ _ hnC, Complex.cpow_one]
    simp only [reciprocalCoeff]
    ring

lemma reciprocalCoeff_norm_le_one {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) :
    ‖reciprocalCoeff χ n‖ ≤ 1 := by
  by_cases hn : n = 0
  · subst n
    simp [reciprocalCoeff]
  · rw [reciprocalCoeff, norm_div, Complex.norm_natCast]
    apply (div_le_one (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))).mpr
    exact (norm_logCoeff_le_one χ n).trans (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn)

lemma reciprocalCoeff_summable_two {q : ℕ} (χ : DirichletCharacter ℂ q) :
    LSeriesSummable (reciprocalCoeff χ) (2 : ℂ) :=
  LSeriesSummable_of_bounded_of_one_lt_re
    (fun n _ => reciprocalCoeff_norm_le_one χ n) (by norm_num)

/-- The scalar Perron formula includes integral cutoffs, where the weight is zero. -/
lemma perron_term_value {n : ℕ} (a : ℕ → ℂ) (hn : n ≠ 0)
    {x σ : ℝ} (hx : 0 < x) (hσ : 1 / 2 ≤ σ) :
    VerticalIntegral' (fun s => LSeries.term a s n * modFivePerronKernel x s) σ =
      if (n : ℝ) ≤ x then a n * ((1 - (n : ℝ) / x : ℝ) : ℂ) else 0 := by
  by_cases heq : x = (n : ℝ)
  · subst x
    have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hf : (fun s => LSeries.term a s n * modFivePerronKernel (n : ℝ) s) =
        fun s => a n * modFivePerronKernel 1 s := by
      funext s
      simpa [hnR.ne'] using modFivePerron_term_kernel a hn hnR s
    rw [hf]
    have hc : VerticalIntegral' (fun s => a n * modFivePerronKernel 1 s) σ =
        a n * VerticalIntegral' (modFivePerronKernel 1) σ := by
      simp only [VerticalIntegral', VerticalIntegral, smul_eq_mul, integral_const_mul]
      ring
    rw [hc, modFivePerron_inversion (by norm_num) hσ]
    simp [modFiveTriangle, hnR.ne']
  · rw [modFivePerron_term_value a hn hx hσ heq]
    have hlt : (n : ℝ) < x ↔ (n : ℝ) ≤ x := lt_iff_le_and_ne.trans
      (and_iff_left (Ne.symm heq))
    simp only [hlt]

/-- Triangular Perron inversion at every positive real cutoff. -/
theorem perron_finite_sum (a : ℕ → ℂ) {x σ : ℝ}
    (hx : 0 < x) (hσ : 1 / 2 ≤ σ) (ha : LSeriesSummable a (σ : ℂ)) :
    VerticalIntegral' (fun s => LSeries a s * modFivePerronKernel x s) σ =
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n * ((1 - (n : ℝ) / x : ℝ) : ℂ) := by
  rw [modFivePerron_series_interchange a hx hσ ha]
  have hz : ∀ n ∉ Finset.Icc 1 ⌊x⌋₊,
      VerticalIntegral' (fun s => LSeries.term a s n * modFivePerronKernel x s) σ = 0 := by
    intro n hn
    by_cases hn0 : n = 0
    · subst n
      simp [VerticalIntegral', VerticalIntegral]
    · rw [perron_term_value a hn0 hx hσ]
      have hnlarge : ⌊x⌋₊ < n := by
        by_contra! h
        exact hn (mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hn0, h⟩)
      exact ite_eq_right (not_le.mpr (Nat.lt_of_floor_lt hnlarge))
  rw [tsum_eq_sum hz]
  apply sum_congr rfl
  intro n hn
  rw [perron_term_value a (by have := (mem_Icc.mp hn).1; omega) hx hσ]
  exact ite_eq_left ((Nat.cast_le.mpr (mem_Icc.mp hn).2).trans (Nat.floor_le hx.le))

/-- The exact Mellin representation required by the finite contour estimate. -/
theorem smoothedReciprocalSum_perron {q : ℕ} (χ : DirichletCharacter ℂ q)
    {x : ℝ} (hx : 0 < x) :
    smoothedReciprocalSum χ x = VerticalIntegral'
      (fun s => LSeries (logCoeff χ) (s + 1) * modFivePerronKernel x s) 2 := by
  rw [smoothedReciprocalSum, ← perron_finite_sum (σ := (2 : ℝ)) (reciprocalCoeff χ) hx
    (by norm_num) (reciprocalCoeff_summable_two χ)]
  simp_rw [reciprocal_series_shift]

#print axioms reciprocal_series_shift
#print axioms perron_finite_sum
#print axioms smoothedReciprocalSum_perron

end RealCharacterTail
