import ReflectedLiouville.Algebra

set_option autoImplicit false
open scoped BigOperators

namespace ReflectedLiouville

/-- Cutoff on the first coordinate, with zero from the library at N−n = 0. -/
noncomputable def prefixReflectedSum (N M : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 M, liouvilleReal n * liouvilleReal (N - n)

/-- The exact whole-divisor atom in the raw form, before normalization. -/
noncomputable def dilatedReflectedSum (N a B : ℕ) : ℝ :=
  ∑ x ∈ (Finset.Icc 1 B).filter (fun x => a ∣ x),
    liouvilleReal x * liouvilleReal (a * N - x)

lemma dilatedReflectedSum_eq_prefix (N a B : ℕ) (ha : 0 < a) :
    dilatedReflectedSum N a B = prefixReflectedSum N (B / a) := by
  classical
  unfold dilatedReflectedSum prefixReflectedSum
  symm
  apply Finset.sum_bij (fun n _ => a * n)
  · intro n hn
    have hn' := Finset.mem_Icc.mp hn
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, dvd_mul_right a n⟩
    · exact Nat.succ_le_of_lt (Nat.mul_pos ha (by omega))
    · have h := (Nat.le_div_iff_mul_le ha).mp hn'.2
      simpa only [Nat.mul_comm] using h
  · intro n hn m hm hnm
    exact Nat.eq_of_mul_eq_mul_left ha hnm
  · intro x hx
    obtain ⟨hx, hdiv⟩ := Finset.mem_filter.mp hx
    obtain ⟨n, hn⟩ := hdiv
    refine ⟨n, ?_, hn.symm⟩
    have hx' := Finset.mem_Icc.mp hx
    rw [hn] at hx'
    apply Finset.mem_Icc.mpr
    refine ⟨by nlinarith, ?_⟩
    apply (Nat.le_div_iff_mul_le ha).mpr
    simpa only [Nat.mul_comm] using hx'.2
  · intro n hn
    exact (liouville_reflected_dilation N a n ha.ne').symm

lemma prefixReflectedSum_at_total (N : ℕ) : prefixReflectedSum N N = reflectedSum N := by
  classical
  unfold prefixReflectedSum reflectedSum reflectedIndices
  symm
  apply Finset.sum_subset
  · intro n hn
    obtain ⟨hnlo, hnhi⟩ := Finset.mem_Ico.mp hn
    exact Finset.mem_Icc.mpr ⟨hnlo, hnhi.le⟩
  · intro n hn hnot
    have hn' := Finset.mem_Icc.mp hn
    have heq : n = N := by
      simp only [Finset.mem_Ico, not_and, not_lt] at hnot
      omega
    simp [heq, liouvilleReal]

lemma prefixReflectedSum_tail_bound (N M : ℕ) (hMN : M ≤ N) :
    |prefixReflectedSum N M - reflectedSum N| ≤ (N - M : ℕ) := by
  classical
  rw [← prefixReflectedSum_at_total]
  have hsub : Finset.Icc 1 M ⊆ Finset.Icc 1 N := by
    intro n hn
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1, (Finset.mem_Icc.mp hn).2.trans hMN⟩
  have heq : prefixReflectedSum N N = prefixReflectedSum N M +
      ∑ n ∈ (Finset.Icc 1 N) \ (Finset.Icc 1 M),
        liouvilleReal n * liouvilleReal (N - n) := by
    unfold prefixReflectedSum
    simpa only [add_comm] using
      (Finset.sum_sdiff (f := fun n => liouvilleReal n * liouvilleReal (N - n)) hsub).symm
  have hdiff : prefixReflectedSum N M - prefixReflectedSum N N =
      -(∑ n ∈ (Finset.Icc 1 N) \ (Finset.Icc 1 M),
        liouvilleReal n * liouvilleReal (N - n)) := by rw [heq]; ring
  rw [hdiff, abs_neg]
  calc
    _ ≤ ∑ n ∈ (Finset.Icc 1 N) \ (Finset.Icc 1 M),
        |liouvilleReal n * liouvilleReal (N - n)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ (Finset.Icc 1 N) \ (Finset.Icc 1 M), (1 : ℝ) :=
      Finset.sum_le_sum (fun n _ => abs_reflected_term_le N n)
    _ = _ := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_sdiff_of_subset hsub]
      simp only [Nat.card_Icc, Nat.add_sub_cancel]

#print axioms dilatedReflectedSum_eq_prefix
#print axioms prefixReflectedSum_tail_bound

end ReflectedLiouville
