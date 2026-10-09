import ReflectedLiouville.PhysicalVolume

set_option autoImplicit false
open scoped BigOperators Classical

namespace ReflectedLiouville

lemma source_support_site_bounds (N : ℕ) (hN : 0 < N) (r k : ℤ) (T : ℝ)
    (hr : 1 ≤ r ∧ r ≤ (N : ℤ)) (hpos : 0 < (N : ℤ) * k + r)
    (hupper : (((N : ℤ) * k + r : ℤ) : ℝ) ≤ T) : 0 ≤ k ∧ (k : ℝ) ≤ T / N := by
  have hn : (0 : ℤ) ≤ N := Int.natCast_nonneg _
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  constructor
  · by_contra hnot
    have hk : k ≤ -1 := by omega
    have hmul := mul_le_mul_of_nonneg_left hk hn
    simp only [mul_neg, mul_one] at hmul
    linarith only [hmul, hr.2, hpos]
  · apply (le_div_iff₀ hNr).mpr
    have hu : (N : ℝ) * (k : ℝ) + (r : ℝ) ≤ T := by
      simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast] using hupper
    have hr0 : (0 : ℝ) ≤ r := by exact_mod_cast (show (0 : ℤ) ≤ r by omega)
    nlinarith only [hu, hr0]

/-- A spacing-N fiber has at most T/N+1 source points, independently of the
    ambient finite block size. -/
theorem source_support_card_le {V : Type*} [Fintype V]
    (N : ℕ) (hN : 0 < N) (site : V → ℤ) (hinj : Function.Injective site)
    (r : ℤ) (hr : 1 ≤ r ∧ r ≤ (N : ℤ)) (T : ℝ) (hT : 0 ≤ T) :
    (((Finset.univ : Finset V).filter (fun i => 0 < (N : ℤ) * site i + r ∧
      (((N : ℤ) * site i + r : ℤ) : ℝ) ≤ T)).card : ℝ) ≤ T / N + 1 := by
  let S := (Finset.univ : Finset V).filter (fun i => 0 < (N : ℤ) * site i + r ∧
    (((N : ℤ) * site i + r : ℤ) : ℝ) ≤ T)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hD : 0 ≤ T / N := div_nonneg hT hNr.le
  have hf : 0 ≤ ⌊T / N⌋ := Int.floor_nonneg.mpr hD
  have hsub : S.image site ⊆ Finset.Icc 0 ⌊T / N⌋ := by
    intro k hk
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨hmem, hpos, hupper⟩ := Finset.mem_filter.mp hi
    have hb := source_support_site_bounds N hN r (site i) T hr hpos hupper
    exact Finset.mem_Icc.mpr ⟨hb.1, Int.le_floor.mpr hb.2⟩
  have hc : S.card ≤ (Finset.Icc (0 : ℤ) ⌊T / N⌋).card := by
    have him : (S.image site).card = S.card := Finset.card_image_of_injective S hinj
    rw [← him]
    exact Finset.card_le_card hsub
  have hcard : (((Finset.Icc (0 : ℤ) ⌊T / N⌋).card : ℝ)) = (⌊T / N⌋ : ℝ) + 1 := by
    have hh := Int.card_Icc_of_le 0 ⌊T / N⌋ (by omega : (0 : ℤ) ≤ ⌊T / N⌋ + 1)
    simp only [sub_zero] at hh
    exact_mod_cast hh
  have hcr : (S.card : ℝ) ≤ ((Finset.Icc (0 : ℤ) ⌊T / N⌋).card : ℝ) := by exact_mod_cast hc
  change (S.card : ℝ) ≤ _
  rw [hcard] at hcr
  linarith only [hcr, Int.floor_le (T / N)]

#print axioms source_support_card_le

end ReflectedLiouville
