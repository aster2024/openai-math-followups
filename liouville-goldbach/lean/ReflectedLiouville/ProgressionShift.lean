import ReflectedLiouville.ProgressionEndpoint

set_option autoImplicit false

namespace ReflectedLiouville

lemma progression_prefix_ordered_shift (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (q : ℕ) (a : ZMod q) (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) (hd : y - x ≤ q) :
    ‖progressionPrefix f q a ⌊y⌋₊ - progressionPrefix f q a ⌊x⌋₊‖ ≤ 1 := by
  have hdelta : 0 ≤ y - x := sub_nonneg.mpr hxy
  have h := short_progression_norm_le_one f hf q a x (y - x) hx hdelta hd
  rw [shortProgressionSum_eq_prefix_difference _ _ _ _ hdelta,
    show x + (y - x) = y by ring] at h
  exact h

lemma progression_prefix_shift (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (q : ℕ) (a : ZMod q) (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hd : |x - y| ≤ q) :
    ‖progressionPrefix f q a ⌊x⌋₊ - progressionPrefix f q a ⌊y⌋₊‖ ≤ 1 := by
  rcases le_total x y with hxy | hyx
  · rw [norm_sub_rev]
    exact progression_prefix_ordered_shift f hf q a x y hx hxy (by have h := (abs_le.mp hd).1; linarith)
  · exact progression_prefix_ordered_shift f hf q a y x hy hyx (abs_le.mp hd).2

/-- Exact two-endpoint cost in the paper's start-average estimate. -/
theorem short_progression_start_shift (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (q : ℕ) (a : ZMod q) (x y H : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hH : 0 ≤ H)
    (hd : |x - y| ≤ q) :
    ‖shortProgressionSum f q a x H - shortProgressionSum f q a y H‖ ≤ 2 := by
  have hlower := progression_prefix_shift f hf q a x y hx hy hd
  have hupper := progression_prefix_shift f hf q a (x + H) (y + H)
    (add_nonneg hx hH) (add_nonneg hy hH) (by simpa only [add_sub_add_right_eq_sub] using hd)
  have hid : shortProgressionSum f q a x H - shortProgressionSum f q a y H =
      (progressionPrefix f q a ⌊x + H⌋₊ - progressionPrefix f q a ⌊y + H⌋₊) -
        (progressionPrefix f q a ⌊x⌋₊ - progressionPrefix f q a ⌊y⌋₊) := by
    rw [shortProgressionSum_eq_prefix_difference _ _ _ H hH,
      shortProgressionSum_eq_prefix_difference _ _ _ H hH]
    ring
  rw [hid]
  have h := norm_sub_le
    (progressionPrefix f q a ⌊x + H⌋₊ - progressionPrefix f q a ⌊y + H⌋₊)
    (progressionPrefix f q a ⌊x⌋₊ - progressionPrefix f q a ⌊y⌋₊)
  linarith

#print axioms short_progression_start_shift

end ReflectedLiouville
