import ReflectedLiouville.RealCutoff

set_option autoImplicit false
open scoped BigOperators

namespace ReflectedLiouville

/-- Summing the real-cutoff dilation atoms. The factor is the exact retained
    reciprocal mass; no averaging of the total N is introduced. -/
theorem raw_sum_dilation_bound {ι : Type*} (I : Finset ι) (N : ℕ)
    (a : ι → ℕ) (T u : ι → ℝ) (η : ℝ)
    (hN : 0 < N) (hη : 0 ≤ η) (hηhalf : η ≤ 1 / 2)
    (ha : ∀ i ∈ I, 0 < a i) (hu : ∀ i ∈ I, 0 ≤ u i)
    (hTlower : ∀ i ∈ I, (1 - η) * (a i : ℝ) * N ≤ T i)
    (hTupper : ∀ i ∈ I, T i ≤ (a i : ℝ) * N) :
    |(∑ i ∈ I, u i * (dilatedReflectedSum N (a i) ⌊T i⌋₊ / T i)) -
      (∑ i ∈ I, u i / a i) * (reflectedSum N / N)| ≤
        (4 * η + 2 / N) * (∑ i ∈ I, u i / a i) := by
  have hNi : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hpoint (i : ι) (hi : i ∈ I) :
      |u i * (dilatedReflectedSum N (a i) ⌊T i⌋₊ / T i) -
        (u i / a i) * (reflectedSum N / N)| ≤
      (4 * η + 2 / N) * (u i / a i) := by
    have hai : (a i : ℝ) ≠ 0 := by exact_mod_cast (ha i hi).ne'
    have hscaled := mul_le_mul_of_nonneg_left
      (real_cutoff_dilation_bound N (a i) (T i) η (ha i hi) hN hη hηhalf
        (hTlower i hi) (hTupper i hi)) (hu i hi)
    have heq : u i * (dilatedReflectedSum N (a i) ⌊T i⌋₊ / T i) -
        (u i / a i) * (reflectedSum N / N) =
      u i * (dilatedReflectedSum N (a i) ⌊T i⌋₊ / T i -
        reflectedSum N / ((a i : ℝ) * N)) := by field_simp
    rw [heq, abs_mul, abs_of_nonneg (hu i hi)]
    convert hscaled using 1 <;> ring
  rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ I, |u i * (dilatedReflectedSum N (a i) ⌊T i⌋₊ / T i) -
        (u i / a i) * (reflectedSum N / N)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ I, (4 * η + 2 / N) * (u i / a i) := Finset.sum_le_sum hpoint
    _ = _ := (Finset.mul_sum _ _ _).symm

#print axioms raw_sum_dilation_bound

end ReflectedLiouville
