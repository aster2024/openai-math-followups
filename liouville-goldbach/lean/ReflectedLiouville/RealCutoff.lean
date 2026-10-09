import ReflectedLiouville.Normalizer

set_option autoImplicit false

namespace ReflectedLiouville

lemma floor_div_natCast (T : ℝ) (a : ℕ) (ha : a ≠ 0) :
    ⌊T⌋₊ / a = ⌊T / (a : ℝ)⌋₊ := by
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  have heq : T = (T / (a : ℝ)) * a := by field_simp
  conv_lhs => rw [heq]
  exact Nat.mul_cast_floor_div_cancel ha _

lemma bin_real_cutoff_bounds (N a : ℕ) (T η : ℝ)
    (ha : 0 < a) (hT : 0 ≤ T)
    (hTlower : (1 - η) * (a : ℝ) * N ≤ T)
    (hTupper : T ≤ (a : ℝ) * N) :
    ⌊T⌋₊ / a ≤ N ∧ ((N - ⌊T⌋₊ / a : ℕ) : ℝ) ≤ N * η + 1 := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hU : T / (a : ℝ) ≤ N := by
    apply (div_le_iff₀ ha').mpr
    simpa only [mul_comm] using hTupper
  have hU₀ : 0 ≤ T / (a : ℝ) := div_nonneg hT ha'.le
  have hfloor := Nat.floor_le hU₀
  have hMN : ⌊T / (a : ℝ)⌋₊ ≤ N := by exact_mod_cast hfloor.trans hU
  rw [floor_div_natCast T a ha.ne']
  refine ⟨hMN, ?_⟩
  rw [Nat.cast_sub hMN]
  have hfl := Nat.lt_floor_add_one (T / (a : ℝ))
  have hUl : (1 - η) * (N : ℝ) ≤ T / a := by
    apply (le_div_iff₀ ha').mpr
    nlinarith [hTlower]
  linarith

/-- The single-bin dilation estimate with a genuine real cutoff and its floor. -/
lemma real_cutoff_dilation_bound (N a : ℕ) (T η : ℝ)
    (ha : 0 < a) (hN : 0 < N) (hη : 0 ≤ η) (hηhalf : η ≤ 1 / 2)
    (hTlower : (1 - η) * (a : ℝ) * N ≤ T)
    (hTupper : T ≤ (a : ℝ) * N) :
    |dilatedReflectedSum N a ⌊T⌋₊ / T - reflectedSum N / ((a : ℝ) * N)| ≤
      (4 * η + 2 / N) / a := by
  have hT : 0 ≤ T := by
    have ha' : (0 : ℝ) < a := by exact_mod_cast ha
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    nlinarith
  obtain ⟨hcut, htail⟩ := bin_real_cutoff_bounds N a T η ha hT hTlower hTupper
  exact normalized_prefix_dilation_bound N a ⌊T⌋₊ T η ha hN hη hηhalf
    hTlower hTupper hcut htail

/-- The ratio hypotheses are precisely the cutoff geometry of a logarithmic bin. -/
lemma bin_ratio_dilation_bound (N a : ℕ) (T η : ℝ)
    (ha : 0 < a) (hN : 0 < N) (hη : 0 ≤ η) (hηhalf : η ≤ 1 / 2)
    (hRatioLower : Real.exp (-η) ≤ T / ((a : ℝ) * N))
    (hRatioUpper : T / ((a : ℝ) * N) ≤ 1) :
    |dilatedReflectedSum N a ⌊T⌋₊ / T - reflectedSum N / ((a : ℝ) * N)| ≤
      (4 * η + 2 / N) / a := by
  have haN : (0 : ℝ) < (a : ℝ) * N := by positivity
  have hexp : 1 - η ≤ Real.exp (-η) := by
    have h := Real.add_one_le_exp (-η)
    linarith
  apply real_cutoff_dilation_bound N a T η ha hN hη hηhalf
  · simpa only [mul_assoc] using (le_div_iff₀ haN).mp (hexp.trans hRatioLower)
  · simpa only [one_mul] using (div_le_iff₀ haN).mp hRatioUpper

#print axioms real_cutoff_dilation_bound

end ReflectedLiouville
