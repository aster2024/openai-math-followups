import ReflectedLiouville.KeptAtomPairing
import ReflectedLiouville.ForcedTargetPairing

set_option autoImplicit false
open scoped BigOperators Classical
open OAI.TwoPointCorrelations

namespace ReflectedLiouville

lemma real_matrix_inner {V : Type*} [Fintype V] [DecidableEq V]
    (A : V → V → ℝ) (f g : V → ℝ) :
    inner ℂ (WithLp.toLp 2 (fun i => (f i : ℂ)))
      (matrixOperator (fun i j => (A i j : ℂ)) (WithLp.toLp 2 (fun i => (g i : ℂ)))) =
      ((∑ i, ∑ j, f i * A i j * g j : ℝ) : ℂ) := by
  rw [PiLp.inner_apply]
  simp only [matrixOperator_apply, RCLike.inner_apply',
    Complex.conj_ofReal, Complex.ofReal_sum, Complex.ofReal_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Both orthogonal endpoint projections are kept in the exact scalar formula. -/
lemma projected_real_matrix_inner {V : Type*} [Fintype V] [DecidableEq V]
    (A : V → V → ℝ) (keep : V → Prop) (f g : V → ℝ) :
    inner ℂ (WithLp.toLp 2 (fun i => (f i : ℂ)))
      ((coordinateProjection keep * matrixOperator (fun i j => (A i j : ℂ)) * coordinateProjection keep)
        (WithLp.toLp 2 (fun i => (g i : ℂ)))) =
      ((∑ i, ∑ j, if keep i ∧ keep j then f i * A i j * g j else 0 : ℝ) : ℂ) := by
  have hsym := (coordinateProjection_selfAdjoint keep).isSymmetric
  change inner ℂ _ (coordinateProjection keep (matrixOperator _ (coordinateProjection keep _))) = _
  have he := hsym (WithLp.toLp 2 (fun i => (f i : ℂ)))
    (matrixOperator (fun i j => (A i j : ℂ)) (coordinateProjection keep (WithLp.toLp 2 (fun i => (g i : ℂ)))))
  change inner ℂ (coordinateProjection keep (WithLp.toLp 2 (fun i => (f i : ℂ)))) _ =
    inner ℂ (WithLp.toLp 2 (fun i => (f i : ℂ))) (coordinateProjection keep _) at he
  rw [← he]
  have hproj (h : V → ℝ) :
      coordinateProjection keep (WithLp.toLp 2 (fun i => (h i : ℂ))) =
        WithLp.toLp 2 (fun i => ((if keep i then h i else 0 : ℝ) : ℂ)) := by
    ext i
    rw [coordinateProjection_apply]
    by_cases hk : keep i <;> simp [hk]
  rw [hproj f, hproj g, real_matrix_inner]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hi : keep i <;> by_cases hj : keep j <;> simp [hi, hj]

#print axioms projected_real_matrix_inner

end ReflectedLiouville
