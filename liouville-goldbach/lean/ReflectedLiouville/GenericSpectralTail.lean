import ReflectedLiouville.GenericAffineMatrixMoment
import OAI.NumberTheory.TwoPoint.Bounds.MatrixSpectralTail

set_option autoImplicit false
open Filter
open scoped BigOperators Classical
open OAI.TwoPointCorrelations

namespace ReflectedLiouville

noncomputable def reflectionTraceBase (J : ℕ) (W : ℝ) : ℝ :=
  Real.exp (4 * J) * (2 * Real.exp 150 * Real.sqrt W) ^ J

noncomputable def reflectionSpectralScale (J : ℕ) (W : ℝ) : ℝ :=
  Real.exp 1 * (2 * reflectionTraceBase J W)

lemma reflectionTraceBase_one_le (J : ℕ) (W : ℝ) (hW : 1 ≤ W) : 1 ≤ reflectionTraceBase J W := by
  have hs : 1 ≤ Real.sqrt W := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hW
  have he : 1 ≤ 2 * Real.exp 150 := by linarith [Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 150)]
  have hinner : 1 ≤ 2 * Real.exp 150 * Real.sqrt W := by
    simpa only [one_mul] using mul_le_mul he hs zero_le_one (by positivity : 0 ≤ 2 * Real.exp 150)
  unfold reflectionTraceBase
  simpa only [one_mul] using mul_le_mul
    (Real.one_le_exp (by positivity : 0 ≤ 4 * (J : ℝ))) (one_le_pow₀ hinner)
    zero_le_one (Real.exp_pos _).le

theorem reflection_affine_spectral_tail (W : ℝ) (hW : 1 ≤ W) :
    ∃ A : ℕ, 1000 ≤ A ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (J M : ℕ) (data : ProhibitedPrimeFamily 1 J M)
        (P : Fin J → Finset ℕ) (α : ℝ), ReflectionTraceRange data P L W α →
        1 ≤ L → ∀ (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ ⌊Real.exp L⌋₊)
          (eligible : ℕ → ℕ → Prop), (∀ d q, eligible d q → (d, q) ∈ data.pairs) →
          ∀ (gate : ((j : Fin J) → P j) → ℤ → ℤ → Prop) (a l U : ℕ),
            (∀ p ∈ data.P ∪ data.Q, l.Coprime p) → Real.exp (L ^ A / 2) ≤ (U : ℝ) →
            uniformAverage (fun x : Fin U => if reflectionSpectralScale J W <
              realMatrixSpectralRadius (reflectionShiftMatrix data P L eligible gate ((a + l * x.val : ℕ) : ℤ))
              then (1 : ℝ) else 0) ≤ Real.exp (-(2 * ⌊L⌋₊ : ℕ)) := by
  obtain ⟨A, hA, hm⟩ := reflection_affine_matrix_moment W hW
  refine ⟨A, hA, ?_⟩
  filter_upwards [hm] with L hmoment
  intro J M data P α hrange hL hB eligible hallowed gate a l U hl hU
  have hUpos : 0 < U := by
    have : (0 : ℝ) < U := (Real.exp_pos _).trans_le hU
    exact_mod_cast this
  letI : Nonempty (Fin U) := ⟨⟨0, hUpos⟩⟩
  have hk : 0 < ⌊L⌋₊ := by
    have hk1 : 1 ≤ ⌊L⌋₊ := Nat.le_floor (by simpa only [Nat.cast_one] using hL)
    omega
  have hb := hmoment J M data P α hrange hL hB eligible hallowed gate a l U hl hU
  change uniformAverage (fun x : Fin U => matrixFrobeniusSq
    (reflectionShiftMatrix data P L eligible gate ((a + l * x.val : ℕ) : ℤ) ^ ⌊L⌋₊)) ≤
      (reflectionTraceBase J W) ^ (2 * ⌊L⌋₊) + 1 at hb
  rw [← FiniteLaw.uniform_average] at hb
  have ht := (FiniteLaw.uniform (Fin U)).matrix_spectral_tail_add_one
    (fun x => reflectionShiftMatrix data P L eligible gate ((a + l * x.val : ℕ) : ℤ))
    ⌊L⌋₊ hk (reflectionTraceBase J W) (reflectionTraceBase_one_le J W hW) hb
  simp only [FiniteLaw.probability, FiniteLaw.uniform_average] at ht
  convert ht using 1
  congr 1

#print axioms reflection_affine_spectral_tail

end ReflectedLiouville
