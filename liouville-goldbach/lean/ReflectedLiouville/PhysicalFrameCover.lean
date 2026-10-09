import ReflectedLiouville.PhysicalPrefixExact
import ReflectedLiouville.PhysicalScalarPairing

set_option autoImplicit false
open scoped Classical

namespace ReflectedLiouville

lemma physical_frame_source_cover (N M B : ℕ) (hN : 0 < N) (T : ℝ)
    (hM : 2 * (B + 1) ≤ M) (hT : T / N ≤ (B : ℝ)) :
    ∀ k : ℕ, k ≤ ⌊T / N⌋₊ → ∃ i : Fin M, (i.val : ℤ) - (M / 2 : ℕ) = (k : ℤ) := by
  intro k hk
  have hkB : k ≤ B := by
    by_cases hnonneg : 0 ≤ T / N
    · have hr := (show (k : ℝ) ≤ (⌊T / N⌋₊ : ℝ) by exact_mod_cast hk).trans (Nat.floor_le hnonneg)
      exact_mod_cast hr.trans hT
    · have hz : ⌊T / N⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
      omega
  apply centered_integer_frame_covers M B hM
  constructor <;> omega

/-- A forced reflected target has the same residue as its source. Its
    signed quotient lies in the frame whenever the negative test is nonzero. -/
lemma physical_frame_target_cover (N M B : ℕ) (hN : 0 < N) (r : ℤ)
    (hr : 1 ≤ r ∧ r ≤ (N : ℤ)) (U L : ℝ) (Q : Finset ℕ)
    (hM : 2 * (B + 1) ≤ M) (hU : U / N + 1 ≤ (B : ℝ))
    (k : ℤ) (d q : ℕ)
    (hG : targetTestValue Q U L ((N : ℤ) * k + r - ((N*q*d : ℕ) : ℤ)) ≠ 0) :
    ∃ i : Fin M,
      (N : ℤ) * ((i.val : ℤ) - (M / 2 : ℕ)) + r =
        (N : ℤ) * k + r - ((N*q*d : ℕ) : ℤ) := by
  let t : ℤ := k - ((q*d : ℕ) : ℤ)
  have he : (N : ℤ) * t + r = (N : ℤ) * k + r - ((N*q*d : ℕ) : ℤ) := by
    dsimp only [t]
    push_cast
    ring
  have hsupport := targetTestValue_support Q U L _ hG
  rw [← he] at hsupport
  have ht := reflected_target_site_bounds N hN r t U hr (by omega) hsupport.2
  have htB : -(B : ℤ) ≤ t ∧ t ≤ (B : ℤ) := by
    have hh : -(t : ℝ) ≤ (B : ℝ) := ht.2.trans hU
    have hlow : -(B : ℝ) ≤ (t : ℝ) := by linarith
    exact ⟨by exact_mod_cast hlow, by have hzero := ht.1; omega⟩
  obtain ⟨i, hi⟩ := centered_integer_frame_covers M B hM t htB
  refine ⟨i, ?_⟩
  rw [hi]
  exact he

#print axioms physical_frame_target_cover
end ReflectedLiouville
