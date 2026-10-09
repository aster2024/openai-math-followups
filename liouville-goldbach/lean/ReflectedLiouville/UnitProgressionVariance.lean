import ReflectedLiouville.BufferedKMTRange

set_option autoImplicit false
open Filter

namespace ReflectedLiouville

/-- The manuscript variance bound for unit classes, with all Q_* and KMT
    conditions discharged. Only the reviewed published KMT and MRT inputs remain. -/
theorem liouville_unit_progression_variance
    (h_KMT : KMTInput) (h_MRT : MRTRealTwistRepulsionInput) :
    ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∃ C X₀ : ℝ, 0 < C ∧ 10 ≤ X₀ ∧
      ∀ (q : ℕ) [NeZero q] (X H : ℝ), X₀ ≤ X → H ≤ X → 10 * (q : ℝ) ≤ H →
        Real.exp ((Real.log X) ^ ν) ≤ H / q →
        unitResidueVariance q X H ≤ C * ((Real.log (H / q)) ^ (-1 / 1000 : ℝ)) *
          (q.totient : ℝ) * X * (H / q) ^ (2 : ℕ) := by
  intro ν hν hν₁
  obtain ⟨C, X₁, hC, hX₁, hunit⟩ := unit_variance_of_reviewed_range h_KMT h_MRT
  obtain ⟨X₂, hX₂⟩ := eventually_atTop.mp (eventually_buffered_kmt_range ν hν)
  refine ⟨C, max X₁ X₂, hC, hX₁.trans (le_max_left _ _), ?_⟩
  intro q inst X H hX hHX hHq hRlower
  have hXX₁ : X₁ ≤ X := (le_max_left _ _).trans hX
  have hXX₂ : X₂ ≤ X := (le_max_right _ _).trans hX
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hq₁ : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hH : 0 < H := by nlinarith
  have hR10 : 10 ≤ H / q := (le_div_iff₀ hq).mpr hHq
  have hRX : H / q ≤ X := by
    apply le_trans _ hHX
    exact (div_le_iff₀ hq).mpr (le_mul_of_one_le_right hH.le hq₁)
  have hrange := hX₂ X hXX₂ q H hHq hHX hRlower
  exact hunit X H _ hXX₁ q (by linarith) hRX hrange

#print axioms liouville_unit_progression_variance

end ReflectedLiouville
