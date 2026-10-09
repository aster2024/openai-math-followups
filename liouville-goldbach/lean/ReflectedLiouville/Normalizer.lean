import ReflectedLiouville.Dilation

set_option autoImplicit false
open scoped BigOperators

namespace ReflectedLiouville

lemma abs_reflectedSum_le (N : ℕ) : |reflectedSum N| ≤ (N : ℝ) := by
  classical
  unfold reflectedSum
  calc
    _ ≤ ∑ n ∈ reflectedIndices N, |liouvilleReal n * liouvilleReal (N - n)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ reflectedIndices N, (1 : ℝ) :=
      Finset.sum_le_sum (fun n _ => abs_reflected_term_le N n)
    _ = ((N - 1 : ℕ) : ℝ) := by simp [reflectedIndices_card]
    _ ≤ _ := by exact_mod_cast Nat.sub_le N 1

/-- Quantified denominator control for the bin's real, unrounded cutoff. -/
lemma normalized_atom_error (s t a N T η : ℝ)
    (ha : 0 < a) (hN : 0 < N) (hη : 0 ≤ η) (hηhalf : η ≤ 1 / 2)
    (hTlower : (1 - η) * a * N ≤ T) (hTupper : T ≤ a * N)
    (habs : |s| ≤ N) (htail : |t - s| ≤ N * η + 1) :
    |t / T - s / (a * N)| ≤ (4 * η + 2 / N) / a := by
  have haN : 0 < a * N := mul_pos ha hN
  have hTpos : 0 < T := by nlinarith
  have hThalf : a * N / 2 ≤ T := by nlinarith
  have hdiff : 0 ≤ a * N - T := sub_nonneg.mpr hTupper
  have hdiffupper : a * N - T ≤ η * (a * N) := by nlinarith
  have hid : t / T - s / (a * N) =
      (t - s) / T + s * ((a * N - T) / (T * (a * N))) := by
    field_simp
    ring
  rw [hid]
  calc
    _ ≤ |(t - s) / T| + |s * ((a * N - T) / (T * (a * N)))| := abs_add_le _ _
    _ = |t - s| / T + |s| * ((a * N - T) / (T * (a * N))) := by
      rw [abs_div, abs_of_pos hTpos, abs_mul,
        abs_of_nonneg (div_nonneg hdiff (by positivity))]
    _ ≤ (N * η + 1) / T + N * (η * (a * N) / (T * (a * N))) := by
      gcongr
    _ = (2 * N * η + 1) / T := by field_simp; ring
    _ ≤ (2 * N * η + 1) / (a * N / 2) := by
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) hThalf
    _ = _ := by field_simp; ring

/-- Finite tail bound transferred to the bin's real normalization. -/
lemma normalized_prefix_dilation_bound (N a B : ℕ) (T η : ℝ)
    (ha : 0 < a) (hN : 0 < N) (hη : 0 ≤ η) (hηhalf : η ≤ 1 / 2)
    (hTlower : (1 - η) * (a : ℝ) * N ≤ T) (hTupper : T ≤ (a : ℝ) * N)
    (hcut : B / a ≤ N) (htail : ((N - B / a : ℕ) : ℝ) ≤ N * η + 1) :
    |dilatedReflectedSum N a B / T - reflectedSum N / ((a : ℝ) * N)| ≤
      (4 * η + 2 / N) / a := by
  rw [dilatedReflectedSum_eq_prefix N a B ha]
  apply normalized_atom_error _ _ _ _ _ _ (by exact_mod_cast ha)
    (by exact_mod_cast hN) hη hηhalf hTlower hTupper (abs_reflectedSum_le N)
  exact (prefixReflectedSum_tail_bound N (B / a) hcut).trans htail

#print axioms normalized_prefix_dilation_bound

end ReflectedLiouville
