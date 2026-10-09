import ReflectedLiouville.OrderedPairs

set_option autoImplicit false

namespace ReflectedLiouville

theorem paper_main_implies_existential :
    PaperMainStatement → ReflectedLogSaving ∧ SignPatternLogSaving := by
  rintro ⟨C, hC, N₀, hN₀, hmain⟩
  have hc : (0 : ℝ) < 1 / (10 : ℝ) ^ (200 : ℕ) := by positivity
  refine ⟨⟨_, hc, C, hC, N₀, hN₀, fun N hN => (hmain N hN).1⟩,
    ⟨_, hc, C, hC, N₀, hN₀, ?_⟩⟩
  intro N hN e₁ e₂ he₁ he₂
  rw [signPatternCount_eq_orderedPairCount]
  exact (hmain N hN).2 e₁ e₂ he₁ he₂

#print axioms paper_main_implies_existential

end ReflectedLiouville
