import ReflectedLiouville.Corollary

set_option autoImplicit false

namespace ReflectedLiouville

lemma reflectedSum_eq_four_counts (N : ℕ) (hN : 2 ≤ N) :
    reflectedSum N =
      (signPatternCount N 1 1 : ℝ) + signPatternCount N (-1) (-1) -
        signPatternCount N 1 (-1) - signPatternCount N (-1) 1 := by
  have hpp := sign_pattern_count_identity N hN 1 1 (Or.inr rfl) (Or.inr rfl)
  have hmm := sign_pattern_count_identity N hN (-1) (-1) (Or.inl rfl) (Or.inl rfl)
  have hpm := sign_pattern_count_identity N hN 1 (-1) (Or.inr rfl) (Or.inl rfl)
  have hmp := sign_pattern_count_identity N hN (-1) 1 (Or.inl rfl) (Or.inr rfl)
  norm_num at hpp hmm hpm hmp
  linarith

lemma linearSum_eq_two_counts (N : ℕ) (hN : 2 ≤ N) :
    linearSum N = (signPatternCount N 1 1 : ℝ) - signPatternCount N (-1) (-1) := by
  have hpp := sign_pattern_count_identity N hN 1 1 (Or.inr rfl) (Or.inr rfl)
  have hmm := sign_pattern_count_identity N hN (-1) (-1) (Or.inl rfl) (Or.inl rfl)
  norm_num at hpp hmm
  linarith

theorem reflected_saving_of_sign_patterns (h : SignPatternLogSaving) : ReflectedLogSaving := by
  obtain ⟨c, hc, C, hC, N₀, hN₀, hbound⟩ := h
  refine ⟨c, hc, 4 * C, by positivity, N₀, hN₀, ?_⟩
  intro N hN
  have hpp := hbound N hN 1 1 (Or.inr rfl) (Or.inr rfl)
  have hmm := hbound N hN (-1) (-1) (Or.inl rfl) (Or.inl rfl)
  have hpm := hbound N hN 1 (-1) (Or.inr rfl) (Or.inl rfl)
  have hmp := hbound N hN (-1) 1 (Or.inl rfl) (Or.inr rfl)
  rw [reflectedSum_eq_four_counts N (by omega)]
  have hcenter :
      (signPatternCount N 1 1 : ℝ) + signPatternCount N (-1) (-1) -
        signPatternCount N 1 (-1) - signPatternCount N (-1) 1 =
      (((signPatternCount N 1 1 : ℝ) - N / 4) +
        ((signPatternCount N (-1) (-1) : ℝ) - N / 4)) -
      (((signPatternCount N 1 (-1) : ℝ) - N / 4) +
        ((signPatternCount N (-1) 1 : ℝ) - N / 4)) := by ring
  rw [hcenter]
  have htri := abs_sub
    (((signPatternCount N 1 1 : ℝ) - N / 4) +
      ((signPatternCount N (-1) (-1) : ℝ) - N / 4))
    (((signPatternCount N 1 (-1) : ℝ) - N / 4) +
      ((signPatternCount N (-1) 1 : ℝ) - N / 4))
  have htri1 := abs_add_le ((signPatternCount N 1 1 : ℝ) - N / 4)
    ((signPatternCount N (-1) (-1) : ℝ) - N / 4)
  have htri2 := abs_add_le ((signPatternCount N 1 (-1) : ℝ) - N / 4)
    ((signPatternCount N (-1) 1 : ℝ) - N / 4)
  calc
    _ ≤ 4 * (C * (N : ℝ) / Real.rpow (Real.log (N : ℝ)) c) := by linarith
    _ = _ := by ring

theorem linear_saving_of_sign_patterns (h : SignPatternLogSaving) : LinearLogSaving := by
  obtain ⟨c, hc, C, hC, N₀, hN₀, hbound⟩ := h
  refine ⟨c, hc, 2 * C, by positivity, N₀, hN₀, ?_⟩
  intro N hN
  have hpp := hbound N hN 1 1 (Or.inr rfl) (Or.inr rfl)
  have hmm := hbound N hN (-1) (-1) (Or.inl rfl) (Or.inl rfl)
  rw [linearSum_eq_two_counts N (by omega)]
  have heq : (signPatternCount N 1 1 : ℝ) - signPatternCount N (-1) (-1) =
      ((signPatternCount N 1 1 : ℝ) - N / 4) -
        ((signPatternCount N (-1) (-1) : ℝ) - N / 4) := by ring
  rw [heq]
  have htri := abs_sub ((signPatternCount N 1 1 : ℝ) - N / 4)
    ((signPatternCount N (-1) (-1) : ℝ) - N / 4)
  calc
    _ ≤ 2 * (C * (N : ℝ) / Real.rpow (Real.log (N : ℝ)) c) := by linarith
    _ = _ := by ring

theorem sign_saving_iff_two_savings :
    SignPatternLogSaving ↔ ReflectedLogSaving ∧ LinearLogSaving :=
  ⟨fun h => ⟨reflected_saving_of_sign_patterns h, linear_saving_of_sign_patterns h⟩,
    fun h => sign_patterns_of_two_savings h.1 h.2⟩

#print axioms reflected_saving_of_sign_patterns
#print axioms sign_saving_iff_two_savings

end ReflectedLiouville
